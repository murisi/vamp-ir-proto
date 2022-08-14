mod ast;
extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::fs;
use std::collections::{BTreeSet, HashMap};
use crate::ast::{Program, Literal, Term, Variable, RelOp, Expression, Clause, ArithOp};

/* If this term is a variable, then give that variable the ID corresponding to
 * its name in the map. If this is not possible, then take out a fresh variable
 * ID and assign that instead. */
fn number_term_variable(
    term: &mut Term,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<String, u32>
) {
    if let Term::Variable(var) = term {
        if let Some(name) = &var.name {
            if let Some(id) = assignments.get(name) {
                var.id = *id;
            } else {
                assignments.insert(name.clone(), *curr_var_id);
                var.id = *curr_var_id;
                *curr_var_id += 1;
            }
        } else {
            var.id = *curr_var_id;
            *curr_var_id += 1;
        }
    }
}

/* Number all the variables occuring in the given expression using the IDs from
 * the given map. In the cases where there's no existing map entry, take out a
 * fresh ID and put that in the map. */
fn number_expr_variables(
    target: &mut Expression,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<String, u32>
) {
    match target {
        Expression::Term(term) => {
            number_term_variable(term, curr_var_id, assignments);
        },
        Expression::Negate(expr) => {
            number_expr_variables(expr, curr_var_id, assignments);
        },
        Expression::Binary(_op, expr1, expr2) => {
            number_expr_variables(expr1, curr_var_id, assignments);
            number_expr_variables(expr2, curr_var_id, assignments);
        }
    }
}

/* Number all the variables occuring in the given clause using the IDs from the
 * given map. In the cases where there's no existing map entry, take out a fresh
 * ID and put that in the map. */
fn number_clause_variables(target: &mut Clause, curr_var_id: &mut u32) {
    let mut assignments = HashMap::<String, u32>::new();
    for term in &mut target.head.terms {
        number_term_variable(term, curr_var_id, &mut assignments);
    }
    for literal in &mut target.body {
        match literal {
            Literal::Predicate(pred) => {
                for term in &mut pred.terms {
                    number_term_variable(term, curr_var_id, &mut assignments);
                }
                for clause in &mut pred.clauses {
                    number_clause_variables(clause, curr_var_id);
                }
            },
            Literal::Relation(_op, expr1, expr2) => {
                number_expr_variables(expr1, curr_var_id, &mut assignments);
                number_expr_variables(expr2, curr_var_id, &mut assignments);
            }
        }
    }
}

/* Number all the variables occuring in the given program using the IDs from the
 * given map. In the cases where there's no existing map entry, take out a fresh
 * ID and put that in the map. */
fn number_program_variables(target: &mut Program, curr_var_id: &mut u32) {
    for query in &mut target.queries {
        let mut assignments = HashMap::<String, u32>::new();
        for term in &mut query.terms {
            number_term_variable(term, curr_var_id, &mut assignments);
        }
    }
    for clauses in target.assertions.values_mut() {
        for clause in clauses {
            number_clause_variables(clause, curr_var_id);
        }
    }
}

/* If this term is a variable, then give that variable the ID corresponding to
 * its ID in the map. If this is not possible, then take out a fresh variable
 * ID and assign that instead. */
fn fresh_term_variable(
    term: &mut Term,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<u32, u32>
) {
    if let Term::Variable(var) = term {
        if let Some(id) = assignments.get(&var.id) {
            var.id = *id;
        } else {
            assignments.insert(var.id, *curr_var_id);
            var.id = *curr_var_id;
            *curr_var_id += 1;
        }
    }
}

/* Number all the variables occuring in the given expression using the IDs from
 * the given map. In the cases where there's no existing map entry, take out a
 * fresh ID and put that in the map. */
fn fresh_expr_variables(
    target: &mut Expression,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<u32, u32>
) {
    match target {
        Expression::Term(term) => {
            fresh_term_variable(term, curr_var_id, assignments);
        },
        Expression::Negate(expr) => {
            fresh_expr_variables(expr, curr_var_id, assignments);
        },
        Expression::Binary(_op, expr1, expr2) => {
            fresh_expr_variables(expr1, curr_var_id, assignments);
            fresh_expr_variables(expr2, curr_var_id, assignments);
        }
    }
}

/* Number all the variables occuring in the given clause using the IDs from the
 * given map. In the cases where there's no existing map entry, take out a fresh
 * ID and put that in the map. */
fn fresh_clause_variables(target: &mut Clause, curr_var_id: &mut u32) {
    let mut assignments = HashMap::<u32, u32>::new();
    for term in &mut target.head.terms {
        fresh_term_variable(term, curr_var_id, &mut assignments);
    }
    for literal in &mut target.body {
        match literal {
            Literal::Predicate(pred) => {
                for term in &mut pred.terms {
                    fresh_term_variable(term, curr_var_id, &mut assignments);
                }
                for clause in &mut pred.clauses {
                    fresh_clause_variables(clause, curr_var_id);
                }
            },
            Literal::Relation(_op, expr1, expr2) => {
                fresh_expr_variables(expr1, curr_var_id, &mut assignments);
                fresh_expr_variables(expr2, curr_var_id, &mut assignments);
            }
        }
    }
}

/* Make sure that the head of each clause comprises entirely of unique
 * variables. Do this be replacing constants and duplicate variables with fresh
 * ones, and by adding equality constraints to the body. This will simplify the
 * substitution of values into clauses. */
fn unique_variable_heads(target: &mut Program, curr_var_id: &mut u32) {
    for clauses in target.assertions.values_mut() {
        for clause in clauses {
            let mut prev_vars = BTreeSet::new();
            for term in &mut clause.head.terms {
                if let Term::Variable(var) = term {
                    if !prev_vars.contains(var) {
                        continue;
                    }
                }
                let new_var = Variable::new(*curr_var_id);
                prev_vars.insert(new_var.clone());
                let new_term = Term::Variable(new_var);
                *curr_var_id += 1;
                clause.body.push(Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(new_term.clone()),
                    Expression::Term(term.clone())
                ));
                *term = new_term;
            }
        }
    }
}

/* Substitute the clauses of the source program into the predicates of the
 * target that reference them. This transformation does not inline the
 * variables. */
fn substitute_program(target: &mut Program, source: Program, curr_var_id: &mut u32) {
    for query in &mut target.queries {
        if let Some(clauses) = source.assertions.get(&query.signature()) {
            query.clauses = clauses.clone();
            for clause in query.clauses.iter_mut() {
                fresh_clause_variables(clause, curr_var_id);
            }
        }
    }
    for clauses in target.assertions.values_mut() {
        for clause in clauses {
            for literal in &mut clause.body {
                if let Literal::Predicate(pred) = literal {
                    if let Some(clauses) = source.assertions.get(&pred.signature()) {
                        pred.clauses = clauses.clone();
                        for clause in pred.clauses.iter_mut() {
                            fresh_clause_variables(clause, curr_var_id);
                        }
                    }
                }
            }
        }
    }
}

/* Produces an expression that is non-zero only if the select line is carrying
 * the given index or if outside the given range. */
fn build_multiplexer(select_line: Expression, idx: usize, size: usize) -> Expression {
    let mut multiplexer = Expression::Term(Term::Constant(1));
    for j in 0..size {
        if j != idx {
            multiplexer = Expression::Binary(
                ArithOp::Times,
                Box::new(multiplexer),
                Box::new(Expression::Binary(
                    ArithOp::Minus,
                    Box::new(select_line.clone()),
                    Box::new(Expression::Term(Term::Constant(j as i32))),
                )),
            );
        }
    }
    multiplexer
}

/* Produces a literal that forces either expr1=expr2 or else_expr=0. */
fn equality_or_sat(expr1: Expression, expr2: Expression, else_expr: Expression) -> Literal {
    Literal::Relation(
        RelOp::Eq,
        Expression::Term(Term::Constant(0)),
        Expression::Binary(
            ArithOp::Times,
            Box::new(else_expr.clone()),
            Box::new(Expression::Binary(
                ArithOp::Minus,
                Box::new(expr1),
                Box::new(expr2),
            ))
        )
    )
}

/* Force each predicate literal in the clause to unify with at least one of the
 * heads of the clauses of the relation it refers to. Return false only if a
 * literal within the clause has no possible unification. */
fn bind_clause_variables(clause: &mut Clause, curr_var_id: &mut u32) -> bool {
    let mut clause_constraints = vec![];
    for literal in &clause.body {
        if let Literal::Predicate(pred) = literal {
            if pred.clauses.is_empty() { return false }
            let select_line =
                Expression::Term(Term::Variable(Variable::new(*curr_var_id)));
            *curr_var_id += 1;
            for (idx, clause) in pred.clauses.iter().enumerate() {
                let multiplexer =
                    build_multiplexer(select_line.clone(), idx, pred.clauses.len());
                
                let assignments = clause
                    .head
                    .terms
                    .iter()
                    .cloned()
                    .zip(pred.terms.iter().cloned());
                /* If the prover selects this clause, then force each parameter
                 * to equal the corresponding head parameter. */
                for (term1, term2) in assignments {
                    clause_constraints.push(equality_or_sat(
                        Expression::Term(term1),
                        Expression::Term(term2),
                        multiplexer.clone(),
                    ));
                }
            }
        }
    }
    clause.body.append(&mut clause_constraints);
    true
}

/* At the top-level, force each predicate literal to unify with at least one of
 * their corresponding clause heads. Delete clauses that have literals with no
 * possible unification. */
fn bind_program_variables(target: &mut Program, curr_var_id: &mut u32) {
    for clauses in target.assertions.values_mut() {
        clauses.retain_mut(|clause| bind_clause_variables(clause, curr_var_id));
    }
}

/* After the addition of multiplexer constraints, the clause bodies contained by
 * predicate literals are equivalent to the predicate literals themselves. So
 * just replace the predicate literals with these clause bodies. */
fn flatten_program(target: &mut Program) {
    for clauses in target.assertions.values_mut() {
        for clause in clauses {
            let mut new_body = vec![];
            for literal in clause.body.drain(..) {
                match literal {
                    Literal::Predicate(p) => {
                        for mut clause in p.clauses {
                            new_body.append(&mut clause.body);
                        }
                    },
                    rel @ Literal::Relation(_, _, _) => {
                        new_body.push(rel);
                    }
                }
            }
            clause.body = new_body;
        }
    }
}

/* Recursive programs cannot be expanded ad-infinitum. Hence when the point is
 * reached when the expansions are sufficient, clauses that still invoke other
 * predicates must be cut-off. */
fn bottom_out_recursion(target: &mut Program) {
    for clauses in target.assertions.values_mut() {
        clauses.retain(|clause| {
            for literal in &clause.body {
                if let Literal::Predicate(_) = literal {
                    return false;
                }
            }
            true
        });
    }
}

/* Substitute the given program into itself the given number of times. This
 * function ensures that each clause instantiation receives fesh variables. */
fn iterate_program(base_program: &Program, pow: u32) -> Program {
    let mut curr_var_id = 0;
    let mut current_program = base_program.clone();
    bottom_out_recursion(&mut current_program);
    number_program_variables(&mut current_program, &mut curr_var_id);

    for _i in 1..pow {
        let mut target_program = base_program.clone();
        number_program_variables(&mut target_program, &mut curr_var_id);
        substitute_program(&mut target_program, current_program, &mut curr_var_id);
        bind_program_variables(&mut target_program, &mut curr_var_id);
        flatten_program(&mut target_program);
        flatten_program_expressions(&mut target_program, &mut curr_var_id);
        current_program = target_program;
    }
    current_program
}

/* Flatten the given expression down to a single term and place the definitions
 * of its parts into the given vector. The parts always take the following form:
 * term1 = -term2 or term1 = term2 OP term3 */
fn flatten_expression(
    expr: &Expression,
    literals: &mut Vec<Literal>,
    curr_var_id: &mut u32,
) -> Term {
    match expr {
        Expression::Term(t) => t.clone(),
        Expression::Negate(n) => {
            let inner = flatten_expression(n, literals, curr_var_id);
            let new_var = Term::Variable(Variable::new(*curr_var_id));
            *curr_var_id += 1;
            let new_term = Literal::Relation(
                RelOp::Eq,
                Expression::Term(new_var.clone()),
                Expression::Negate(Box::new(Expression::Term(inner)))
            );
            literals.push(new_term);
            new_var
        },
        Expression::Binary(op, e1, e2) => {
            let inner1 = flatten_expression(e1, literals, curr_var_id);
            let inner2 = flatten_expression(e2, literals, curr_var_id);
            let new_var = Term::Variable(Variable::new(*curr_var_id));
            *curr_var_id += 1;
            let new_term = Literal::Relation(
                RelOp::Eq,
                Expression::Term(new_var.clone()),
                Expression::Binary(
                    op.clone(),
                    Box::new(Expression::Term(inner1)),
                    Box::new(Expression::Term(inner2)),
                )
            );
            literals.push(new_term);
            new_var
        }
    }
}

/* If the given literal contains expression trees, then produce an equivalent
 * literal that uses only one expression tree of height one. */
fn flatten_literal_expressions(
    literal: Literal,
    literals: &mut Vec<Literal>,
    curr_var_id: &mut u32,
) -> Literal {
    match literal.clone() {
        Literal::Relation(RelOp::Ne, _, _) =>
            unreachable!("not equal literals should not be present at this stage"),
        Literal::Predicate(_) => literal,
        // If the given literal is already in three address from, then do not
        // try to flatten it again
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(_),
            Expression::Term(_),
        ) => literal,
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(_),
            Expression::Negate(e),
        ) if matches!(&*e, Expression::Term(_)) => literal,
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(_),
            Expression::Binary(_, e1, e2),
        ) if matches!((&*e1, &*e2), (Expression::Term(_), Expression::Term(_))) => literal,
        // Literal is not in three address form, so flatten it
        Literal::Relation(RelOp::Eq, e1, e2) => {
            let lhs_term = flatten_expression(
                &Expression::Binary(
                    ArithOp::Minus,
                    Box::new(e1.clone()),
                    Box::new(e2.clone()),
                ),
                literals,
                curr_var_id
            );
            Literal::Relation(
                RelOp::Eq,
                Expression::Term(lhs_term),
                Expression::Term(Term::Constant(0))
            )
        }
    }
}

/* Flatten all expressions occuring in the clause, creating additional literals
 * as necessary. */
fn flatten_clause_expressions(
    clause: &mut Clause,
    curr_var_id: &mut u32,
) {
    let mut expr_literals = Vec::new();
    for literal in clause.body.iter_mut() {
        *literal = flatten_literal_expressions(
            literal.clone(),
            &mut expr_literals,
            curr_var_id,
        );
    }
    clause.body.append(&mut expr_literals);
}

/* Flatten all expressions occuring in the program, creating additional clause
 * literals as necessary. */
fn flatten_program_expressions(
    program: &mut Program,
    curr_var_id: &mut u32,
) {
    for clauses in program.assertions.values_mut() {
        for clause in clauses {
            flatten_clause_expressions(clause, curr_var_id);
        }
    }
}

fn main() {
    let unparsed_file = fs::read_to_string("tests/transitive.pir").expect("cannot read file");
    let orig_program = Program::parse(&unparsed_file).unwrap();
    println!("{:#?}", iterate_program(&orig_program, 3));
}
