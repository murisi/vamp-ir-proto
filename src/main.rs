mod ast;
mod transform;
use ark_ff::PrimeField;
use ark_ec::{AffineCurve, ProjectiveCurve, TEModelParameters};
use ark_bls12_381::{Bls12_381, Fr as BlsScalar};
use ark_ed_on_bls12_381::{
    EdwardsParameters as JubJubParameters, Fr as JubJubScalar,
};
use plonk_core::circuit::{verify_proof, Circuit};
use ark_poly_commit::{sonic_pc::SonicKZG10, PolynomialCommitment};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_ec::models::twisted_edwards_extended::GroupAffine;
use rand_core::OsRng;
use plonk::error::to_pc_error;
use plonk_core::constraint_system::StandardComposer;
use plonk_core::error::Error;
use std::fs;
use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;
use crate::ast::{Program, Literal, Expression, ArithOp, RelOp, Term};
use crate::transform::{iterate_program, collect_program_variables, build_explicit_defs};
extern crate pest;
#[macro_use]
extern crate pest_derive;

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
        let make_constant = |c: i32| -> F {
            if c >= 0 {
                F::from(c as u32)
            } else {
                -F::from((-c) as u32)
            }
        };
        let mut inputs = BTreeMap::new();
        for (var, field_elt) in &self.variable_map {
            inputs.insert(var, composer.add_input(*field_elt));
        }
        let zero = composer.zero_var();
        for literal in &self.program.literals {
            match literal.clone() {
                Literal::Predicate(_) =>
                    panic!("compilation should leave no predicates"),
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
                            .constant(make_constant(c2))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(-(make_constant(*c2)/make_constant(*c3)))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -(F::one()/make_constant(*c3)))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .mul(F::one())
                            .constant(-make_constant(*c2))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], zero, Some(zero))
                            .add(F::one(), F::zero())
                            .constant(-(make_constant(*c2)*make_constant(*c3)))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v2], Some(zero))
                            .add(F::one(), -make_constant(*c3))
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
                    composer.arithmetic_gate(|gate| {
                        gate.witness(inputs[&v1], inputs[&v3], Some(zero))
                            .add(F::one(), -make_constant(*c2))
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
                _ => {}
            }
        }
        Ok(())
    }

    fn padded_circuit_size(&self) -> usize {
        1 << 9
    }
}

fn main() {
    let unparsed_file = fs::read_to_string("tests/transitive.pir").expect("cannot read file");
    let orig_program = Program::parse(&unparsed_file).unwrap();
    build_explicit_defs(&orig_program);
    let compiled_program = iterate_program(&orig_program, 3);
    println!("{:#?}", compiled_program);
    // Generate CRS
    type PC = SonicKZG10<Bls12_381, DensePolynomial<BlsScalar>>;
    let pp = PC::setup(1 << 10, None, &mut OsRng)
        .map_err(to_pc_error::<BlsScalar, PC>)
        .expect("unable to setup polynomial commitment scheme public parameters");
    let mut circuit = PlonkProgram::<BlsScalar, JubJubParameters>::new(compiled_program);
    // Compile the circuit
    let (pk_p, vk) = circuit.compile::<PC>(&pp).expect("unable to compile circuit");

    let (x, y) = JubJubParameters::AFFINE_GENERATOR_COEFFS;
    let generator: GroupAffine<JubJubParameters> = GroupAffine::new(x, y);
    let point_f_pi: GroupAffine<JubJubParameters> =
        AffineCurve::mul(&generator, JubJubScalar::from(2u64).into_repr())
            .into_affine();
}
