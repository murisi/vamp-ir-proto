mod ast;
mod transform;
use ark_ff::PrimeField;
use ark_ec::TEModelParameters;
use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ed_on_bls12_381::EdwardsParameters as JubJubParameters;
use plonk_core::circuit::{verify_proof, Circuit};
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use ark_poly::polynomial::univariate::DensePolynomial;
use rand_core::OsRng;
use plonk::error::to_pc_error;
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use std::fs;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::marker::PhantomData;
use crate::ast::{Program, Literal, Expression, ArithOp, RelOp, Term, Predicate, Clause};
use std::io::Write;
use plonk_core::prelude::VerifierData;
use crate::transform::{compile_program, collect_program_variables};
extern crate pest;
#[macro_use]
extern crate pest_derive;

// Make field elements from signed values
fn make_constant<F: PrimeField>(c: i32) -> F {
    if c >= 0 {
        F::from(c as u32)
    } else {
        -F::from((-c) as u32)
    }
}

struct PlonkProgram<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>, {
    program: Program,
    variable_map: BTreeMap<ast::Variable, F>,
    phantom: PhantomData<P>,
}

impl<F, P> PlonkProgram<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    fn new(program: Program) -> PlonkProgram<F, P> {
        let mut variables = BTreeSet::new();
        collect_program_variables(&program, &mut variables);
        let mut variable_map = BTreeMap::new();
        for variable in variables {
            variable_map.insert(variable, F::default());
        }
        PlonkProgram { program, variable_map, phantom: PhantomData }
    }

    /* Populate the input and auxilliary variables from the given program inputs
       and choice points. */
    fn populate_variables(
        &mut self,
        var_assignments: BTreeMap<ast::Variable, i32>,
        choice_points: HashMap<Vec<usize>, i32>
    ) {
        // Get the definitions necessary to populate auxiliary variables
        let mut definitions = self.program.definitions.clone();
        // Hard-code constant definitions for choice points and variable
        // assignments
        let mut remaining_choices: BTreeSet<_> =
            self.program.choice_points.values().collect();
        for (path, choice) in &choice_points {
            let choice_var = self.program.choice_points[path].clone();
            remaining_choices.remove(&choice_var);
            definitions.insert(choice_var, Expression::Term(Term::Constant(*choice)));
        }
        // Set the remaining choices to arbitrary values since they will be
        // cancelled out in computations
        for choice_var in remaining_choices {
            definitions.insert(choice_var.clone(), Expression::Term(Term::Constant(0)));
        }
        for (var, value) in &var_assignments {
            definitions.insert(var.clone(), Expression::Term(Term::Constant(*value)));
        }
        // Start deriving witnesses
        for (var, value) in &mut self.variable_map {
            let var_expr = Expression::Term(Term::Variable(var.clone()));
            let expr_val = evaluate_expr(&var_expr, &mut definitions);
            *value = make_constant(expr_val);
        }
    }
}

impl<F, P> Circuit<F, P> for PlonkProgram<F, P>
where
    F: PrimeField,
    P: TEModelParameters<BaseField = F>,
{
    const CIRCUIT_ID: [u8; 32] = [0xff; 32];

    fn gadget(
        &mut self,
        composer: &mut StandardComposer<F, P>,
    ) -> Result<(), Error> {
        let mut inputs = BTreeMap::new();
        for (var, field_elt) in &self.variable_map {
            inputs.insert(var, composer.add_input(*field_elt));
        }
        let zero = composer.zero_var();
        for literal in &self.program.body {
            match literal.clone() {
                Literal::Predicate(_) =>
                    panic!("compilation should leave no predicates"),
                // Variables on the LHS
                // v1 = v2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Term(Term::Variable(v2)),
                ) => {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -F::one())
                    });
                },
                // v1 = c2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Term(Term::Constant(c2)),
                ) => {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(-c2))
                    });
                },
                // v1 = -c2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Negate(e2),
                ) if matches!(&*e2, Expression::Term(Term::Constant(c2)) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(*c2))
                    });
                    true
                }) => {},
                // v1 = -v2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Negate(e2),
                ) if matches!(&*e2, Expression::Term(Term::Variable(v2)) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), F::one())
                    });
                    true
                }) => {},
                // v1 = c2 + c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(-c2-c3))
                    });
                    true
                }) => {},
                // v1 = v2 + c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -F::one())
                            .constant(make_constant(-c3))
                    });
                    true
                }) => {},
                // v1 = c2 + v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .add(F::one(), -F::one())
                            .constant(make_constant(-c2))
                    });
                    true
                }) => {},
                // v1 = v2 + v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(inputs[&v3]))
                            .add(F::one(), -F::one())
                            .out(-F::one())
                    });
                    true
                }) => {},
                // v1 = c2 - c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(-c2+c3))
                    });
                    true
                }) => {},
                // v1 = v2 - c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -F::one())
                            .constant(make_constant(*c3))
                    });
                    true
                }) => {},
                // v1 = c2 - v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .add(F::one(), F::one())
                            .constant(make_constant(-c2))
                    });
                    true
                }) => {},
                // v1 = v2 - v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(inputs[&v3]))
                            .add(F::one(), -F::one())
                            .out(F::one())
                    });
                    true
                }) => {},
                // v1 = c2 / c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(*c2);
                    let op2: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(-(op1/op2))
                    });
                    true
                }) => {},
                // v1 = v2 / c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op2: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -(F::one()/op2))
                    });
                    true
                }) => {},
                // v1 = c2 / v3 ***
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op1: F = make_constant(*c2);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .mul(F::one())
                            .constant(-op1)
                    });
                    true
                }) => {},
                // v1 = v2 / v3 ***
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(inputs[&v2]))
                            .mul(F::one())
                            .out(-F::one())
                    });
                    true
                }) => {},
                // v1 = c2 * c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(*c2);
                    let op2: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(-(op1*op2))
                    });
                    true
                }) => {},
                // v1 = v2 * c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op2: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -op2)
                    });
                    true
                }) => {},
                // v1 = c2 * v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op2: F = make_constant(*c2);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .add(F::one(), -op2)
                    });
                    true
                }) => {},
                // v1 = v2 * v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], inputs[&v3], Some(inputs[&v1]))
                            .mul(F::one())
                            .out(-F::one())
                    });
                    true
                }) => {},
                // Now for constants on the LHS
                // c1 = v2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Term(Term::Variable(v2)),
                ) => {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(-c1))
                    });
                },
                // c1 = c2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Term(Term::Constant(c2)),
                ) => {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(make_constant(c2-c1))
                    });
                },
                // c1 = -c2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Negate(e2),
                ) if matches!(&*e2, Expression::Term(Term::Constant(c2)) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(make_constant(c1+*c2))
                    });
                    true
                }) => {},
                // c1 = -v2
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Negate(e2),
                ) if matches!(&*e2, Expression::Term(Term::Variable(v2)) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(c1))
                    });
                    true
                }) => {},
                // c1 = c2 + c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(make_constant(c1-c2-c3))
                    });
                    true
                }) => {},
                // c1 = v2 + c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(c3-c1))
                    });
                    true
                }) => {},
                // c1 = c2 + v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v3], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(c2-c1))
                    });
                    true
                }) => {},
                // c1 = v2 + v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Plus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], inputs[&v3], Some(zero))
                            .add(F::one(), F::one())
                            .constant(make_constant(-c1))
                    });
                    true
                }) => {},
                // c1 = c2 - c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(make_constant(c2-c3-c1))
                    });
                    true
                }) => {},
                // c1 = v2 - c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(-*c3-c1))
                    });
                    true
                }) => {},
                // c1 = c2 - v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v3], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(make_constant(c1-c2))
                    });
                    true
                }) => {},
                // c1 = v2 - v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Minus, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], inputs[&v3], Some(zero))
                            .add(F::one(), -F::one())
                            .constant(make_constant(-c1))
                    });
                    true
                }) => {},
                // c1 = c2 / c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op2: F = make_constant(*c2);
                    let op3: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(op1-(op2/op3))
                    });
                    true
                }) => {},
                // c1 = v2 / c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op3: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(-(op1*op3))
                    });
                    true
                }) => {},
                // c1 = c2 / v3 ***
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op2: F = make_constant(*c2);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v3], zero, Some(zero))
                            .constant(-(op2/op1))
                    });
                    true
                }) => {},
                // c1 = v2 / v3 ***
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Divide, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op1: F = make_constant(c1);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], inputs[&v3], Some(zero))
                            .add(F::one(), -op1)
                    });
                    true
                }) => {},
                // c1 = c2 * c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op2: F = make_constant(*c2);
                    let op3: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(zero, zero, Some(zero))
                            .add(F::zero(), F::zero())
                            .constant(op1-(op2*op3))
                    });
                    true
                }) => {},
                // c1 = v2 * c3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Constant(c3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op3: F = make_constant(*c3);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], zero, Some(zero))
                            .add(op3, F::zero())
                            .constant(-op1)
                    });
                    true
                }) => {},
                // c1 = c2 * v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Constant(c2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op1: F = make_constant(c1);
                    let op2: F = make_constant(*c2);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v3], zero, Some(zero))
                            .add(op2, F::zero())
                            .constant(-op1)
                    });
                    true
                }) => {},
                // c1 = v2 * v3
                Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Constant(c1)),
                    Expression::Binary(ArithOp::Times, e2, e3),
                ) if matches!((&*e2, &*e3), (
                    Expression::Term(Term::Variable(v2)),
                    Expression::Term(Term::Variable(v3)),
                ) if {
                    let op1: F = make_constant(c1);
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v2], inputs[&v3], Some(zero))
                            .mul(F::one())
                            .out(-op1)
                    });
                    true
                }) => {},
                _ => panic!("unsupported constraint encountered")
            }
        }
        Ok(())
    }

    fn padded_circuit_size(&self) -> usize {
        1 << 10
    }
}

/* Evaluate the given expression sourcing any variables from the given map. */
fn evaluate_expr(expr: &Expression, defs: &mut BTreeMap<ast::Variable, Expression>) -> i32 {
    match expr {
        Expression::Term(Term::Constant(c)) => *c,
        Expression::Term(Term::Variable(v)) => {
            let val = evaluate_expr(&defs[v].clone(), defs);
            defs.insert(v.clone(), Expression::Term(Term::Constant(val)));
            val
        },
        Expression::Negate(e) => -evaluate_expr(e, defs),
        Expression::Binary(ArithOp::Plus, a, b) =>
            evaluate_expr(&a, defs) +
            evaluate_expr(&b, defs),
        Expression::Binary(ArithOp::Minus, a, b) =>
            evaluate_expr(&a, defs) -
            evaluate_expr(&b, defs),
        Expression::Binary(ArithOp::Times, a, b) =>
            evaluate_expr(&a, defs) *
            evaluate_expr(&b, defs),
        Expression::Binary(ArithOp::Divide, a, b) =>
            evaluate_expr(&a, defs) /
            evaluate_expr(&b, defs),
    }
}

/* Run the given expression in the context of the supplied variable mappings. */
fn run_expr(expr: &Expression, bindings: &mut BTreeMap<ast::Variable, i32>) -> i32 {
    match expr {
        Expression::Term(Term::Constant(c)) => *c,
        Expression::Term(Term::Variable(v)) => bindings[v],
        Expression::Negate(e) => -run_expr(e, bindings),
        Expression::Binary(ArithOp::Plus, a, b) =>
            run_expr(&a, bindings) +
            run_expr(&b, bindings),
        Expression::Binary(ArithOp::Minus, a, b) =>
            run_expr(&a, bindings) -
            run_expr(&b, bindings),
        Expression::Binary(ArithOp::Times, a, b) =>
            run_expr(&a, bindings) *
            run_expr(&b, bindings),
        Expression::Binary(ArithOp::Divide, a, b) =>
            run_expr(&a, bindings) /
            run_expr(&b, bindings),
    }
}

/* Run the clause (with head variables substituted in from the supplied map) in
 * the context of the given program. */
fn run_clause(
    clause: &Clause,
    program: &Program,
    bindings: &mut BTreeMap<ast::Variable, i32>,
    max_depth: u32,
) -> Result<HashMap<Vec<usize>, i32>, Literal> {
    let mut choice_points = HashMap::new();
    for (literal_idx, literal) in clause.body.iter().enumerate() {
        match literal {
            // Treat equalities with a variable on the LHS as a definition and
            // update the bindings accordingly
            Literal::Relation(
                RelOp::Eq,
                Expression::Term(Term::Variable(v)),
                rhs
            ) => {
                let rhs_val = run_expr(&rhs, bindings);
                match bindings.get(&v) {
                    Some(lhs_val) if *lhs_val == rhs_val => {},
                    Some(_lhs_val) => return Err(literal.clone()),
                    None => { bindings.insert(v.clone(), rhs_val); },
                }
            },
            // Otherwise just check the given constraints
            Literal::Relation(RelOp::Eq, lhs, rhs) => {
                if run_expr(&lhs, bindings) != run_expr(&rhs, bindings) {
                    return Err(literal.clone())
                }
            },
            Literal::Relation(RelOp::Ne, lhs, rhs) => {
                if run_expr(&lhs, bindings) == run_expr(&rhs, bindings) {
                    return Err(literal.clone())
                }
            },
            Literal::Predicate(pred) => {
                let inner_choice_points = run_query(&pred, program, bindings, max_depth)?;
                for (mut path, val) in inner_choice_points {
                    path.insert(0, literal_idx);
                    choice_points.insert(path, val);
                }
            }
        }
    }
    Ok(choice_points)
}

/* Attempts to assign term2 to term1, modifying rbindings as necessary. Returns
 * false if the two terms do not unify. */
fn unify_terms(
    term1: &Term,
    rbindings: &mut BTreeMap<ast::Variable, i32>,
    term2: &Term,
    cbindings: &BTreeMap<ast::Variable, i32>
) -> bool {
    match (term1, term2) {
        (Term::Constant(c1), Term::Constant(c2))
            if c1 != c2 => return false,
        (Term::Constant(c1), Term::Variable(v2))
            if *c1 != cbindings[v2] => return false,
        (Term::Variable(v1), Term::Variable(v2))
            if !rbindings.contains_key(&v1) => {
                rbindings.insert(v1.clone(), cbindings[v2]);
            },
        (Term::Variable(v1), Term::Variable(v2))
            if rbindings.get(&v1) != Some(&cbindings[v2]) => return false,
        (Term::Variable(v1), Term::Constant(c2))
            if !rbindings.contains_key(&v1) => {
                rbindings.insert(v1.clone(), *c2);
            },
        (Term::Variable(v1), Term::Constant(c2))
            if rbindings.get(&v1) != Some(&c2) => return false,
        _ => return true,
    }
    true
}

/* Runs the given predicate (with non-explicit variables substituted in from the
 * map) against the program and updates the binding map with the computed
 * explicit variables. */
fn run_query(
    query: &Predicate,
    program: &Program,
    bindings: &mut BTreeMap<ast::Variable, i32>,
    max_depth: u32,
) -> Result<HashMap<Vec<usize>, i32>, Literal> {
    // Do not look for deeper solutions because they will not be represented in
    // the circuit
    if max_depth == 0 { return Err(Literal::Predicate(query.clone())) }
    // Search for a clause that proves the given predicate
    let clauses = program.assertions[&query.signature()].iter();
    'search: for (clause_idx, clause) in clauses.enumerate() {
        // Bind the implicit variables to current clause head
        let mut cbindings = BTreeMap::new();
        let arg_params = query.terms.iter().zip(clause.head.terms.iter());
        for (i, (term1, term2)) in arg_params.enumerate() {
            if !clause.explicits[i] &&
                !unify_terms(term2, &mut cbindings, term1, bindings) {
                    continue 'search
            }
        }
        // Attempt to run the clause
        let mut choice_points = if let Ok(icp) = run_clause(
            clause,
            program,
            &mut cbindings,
            max_depth-1,
        ) {
            icp
        } else {
            continue 'search
        };
        // Bind the explicit variables from the current clause head
        let mut rbindings = bindings.clone();
        let arg_params = query.terms.iter().zip(clause.head.terms.iter());
        for (i, (term1, term2)) in arg_params.enumerate() {
            if clause.explicits[i] &&
                !unify_terms(term1, &mut rbindings, term2, &cbindings) {
                    continue 'search
            }
        }
        *bindings = rbindings;
        choice_points.insert(vec![], clause_idx as i32);
        return Ok(choice_points)
    }
    Err(Literal::Predicate(query.clone()))
}

/* Prompt for satisfying inputs to the given program and derive the choice
 * points that prove them. */
fn prompt_inputs(
    annotated: &Program,
    compiled: &Program,
    max_depth: u32,
) ->(BTreeMap<ast::Variable, i32>, HashMap<Vec<usize>, i32>) {
    let mut var_assignments = BTreeMap::new();
    let mut choice_points = HashMap::new();
    // Solicit input variables from user and solve for choice point values
    for (query_idx, query) in annotated.queries.iter().enumerate() {
        println!("Query: {:?}", query);
        let mut bindings = BTreeMap::new();
        for (term_idx, term) in query.terms.iter().enumerate() {
            if let Term::Variable(v) = term {
                print!("{:?}: ", v);
                std::io::stdout().flush().expect("flush failed!");
                let mut input_line = String::new();
                std::io::stdin()
                    .read_line(&mut input_line)
                    .expect("failed to read input");
                let x: i32 = input_line.trim().parse().expect("input not an integer");
                bindings.insert(v.clone(), x);
                let compiled_var = &compiled.queries[query_idx].terms[term_idx];
                if let Term::Variable(v) = compiled_var {
                    var_assignments.insert(v.clone(), x);
                }
            }
        }
        let inner_choice_points = run_query(query, &annotated, &mut bindings, max_depth).unwrap();
        for (mut path, choice) in inner_choice_points {
            path.insert(0, query_idx);
            choice_points.insert(path, choice);
        }
    }
    (var_assignments, choice_points)
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() < 2 {
        panic!("please supply the vamp-ir file path");
    } else if args.len() < 3 {
        panic!("please supply the iteration count");
    }
    let unparsed_file = fs::read_to_string(args[1].clone()).expect("cannot read file");
    let orig_program = Program::parse(&unparsed_file).unwrap();
    let iter_count = args[2].parse().expect("unable to parse iteration count");
    println!("{:#?}\n", orig_program);
    println!("Compiling...");
    let (annotated_program, compiled_program) = compile_program(&orig_program, iter_count);
    
    // Generate CRS
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 10, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)
        .expect("unable to setup polynomial commitment scheme public parameters");
    let mut circuit = PlonkProgram::<BlsScalar, JubJubParameters>::new(compiled_program.clone());
    // Compile the circuit
    let (pk_p, vk) = circuit.compile::<PC>(&pp).expect("unable to compile circuit");
    
    // Prover POV
    println!("Proving...");
    let mut circuit = PlonkProgram::<BlsScalar, JubJubParameters>::new(compiled_program.clone());
    // Prompt for program inputs
    let (var_assignments, choice_points) = prompt_inputs(
        &annotated_program,
        &compiled_program,
        iter_count,
    );
    // Populate variable definitions
    circuit.populate_variables(var_assignments, choice_points);
    // Start proving witnesses
    let (proof, pi) = circuit.gen_proof::<PC>(&pp, pk_p, b"Test").unwrap();

    // Verifier POV
    println!("Verifying...");
    let verifier_data = VerifierData::new(vk, pi);
    let verifier_result = verify_proof::<BlsScalar, JubJubParameters, PC>(
        &pp,
        verifier_data.key,
        &proof,
        &verifier_data.pi,
        b"Test",
    );
    println!("Verifier Result: {:?}", verifier_result);
}
