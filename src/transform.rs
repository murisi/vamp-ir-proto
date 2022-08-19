use std::collections::{BTreeSet, HashMap, BTreeMap};
use petgraph::Graph;
use petgraph::algo::tarjan_scc;
use crate::ast::{Signature, Program, Literal, Term, Variable, RelOp, Expression, Clause, ArithOp, Predicate};

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

/* Give the given variable an ID corresponding to its ID in the map. If this is
 * not possible, then take out a fresh variable ID and assign that instead. */
fn fresh_variable(
    var: &mut Variable,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<u32, u32>,
) {
    if let Some(id) = assignments.get(&var.id) {
        var.id = *id;
    } else {
        assignments.insert(var.id, *curr_var_id);
        var.id = *curr_var_id;
        *curr_var_id += 1;
    }
}

/* If this term is a variable, then give that variable the ID corresponding to
 * its ID in the map. If this is not possible, then take out a fresh variable
 * ID and assign that instead. */
fn fresh_term_variable(
    term: &mut Term,
    curr_var_id: &mut u32,
    assignments: &mut HashMap<u32, u32>,
) {
    if let Term::Variable(var) = term {
        fresh_variable(var, curr_var_id, assignments);
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
    let mut new_definitions = BTreeMap::<Variable, Expression>::new();
    for (mut var, mut expr) in target.definitions.clone() {
        fresh_variable(&mut var, curr_var_id, &mut assignments);
        fresh_expr_variables(&mut expr, curr_var_id, &mut assignments);
        new_definitions.insert(var, expr);
    }
    target.definitions = new_definitions;
    for var in &mut target.choice_points.values_mut() {
        fresh_variable(var, curr_var_id, &mut assignments);
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

/* Produce the given binary operation making sure to do any straightforward
 * simplifications. */
fn binary_operation(op: ArithOp, e1: Expression, e2: Expression) -> Expression {
    match (op, e1, e2) {
        (ArithOp::Times, Expression::Term(Term::Constant(1)), e2) => e2,
        (ArithOp::Times, e1, Expression::Term(Term::Constant(1))) => e1,
        (ArithOp::Times, e1 @ Expression::Term(Term::Constant(0)), _) => e1,
        (ArithOp::Times, _, e2 @ Expression::Term(Term::Constant(0))) => e2,
        (ArithOp::Divide, e1, Expression::Term(Term::Constant(1))) => e1,
        (ArithOp::Plus, Expression::Term(Term::Constant(0)), e2) => e2,
        (ArithOp::Plus, e1, Expression::Term(Term::Constant(0))) => e1,
        (ArithOp::Minus, e1, Expression::Term(Term::Constant(0))) => e1,
        (op, e1, e2) => Expression::Binary(op, Box::new(e1), Box::new(e2))
    }
}

/* Produces an expression that is non-zero only if the select line is carrying
 * the given index or if outside the given range. */
fn build_multiplexer(select_line: Expression, idx: usize, size: usize) -> Expression {
    let mut multiplexer = Expression::Term(Term::Constant(1));
    for j in 0..size {
        if j != idx {
            multiplexer = binary_operation(
                ArithOp::Times,
                multiplexer,
                binary_operation(
                    ArithOp::Minus,
                    select_line.clone(),
                    Expression::Term(Term::Constant(j as i32)),
                ),
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
        binary_operation(
            ArithOp::Times,
            else_expr.clone(),
            binary_operation(
                ArithOp::Minus,
                expr1,
                expr2,
            )
        )
    )
}

/* Force the given predicate literal to unify with at least one of the heads of
 * the clauses of the relation it refers to. Return false only if this predicate
 * has no possible unification. */
fn bind_predicate_variables(
    pred: &mut Predicate,
    constraints: &mut Vec<Literal>,
    definitions: &mut BTreeMap<Variable, Expression>,
    curr_var_id: &mut u32,
) -> Option<Variable> {
    if pred.clauses.is_empty() { return None }
    let clause_count = pred.clauses.len();
    let select_var = Variable::new(*curr_var_id);
    let select_line = Expression::Term(Term::Variable(select_var.clone()));
    *curr_var_id += 1;
    for (idx, clause) in pred.clauses.iter_mut().enumerate() {
        let multiplexer =
            build_multiplexer(select_line.clone(), idx, clause_count);
        
        let assignments = clause
            .head
            .terms
            .iter()
            .cloned()
            .zip(pred.terms.iter().cloned());
        /* If the prover selects this clause, then force each parameter
         * to equal the corresponding head parameter. */
        for (i, (term1, term2)) in assignments.enumerate() {
            constraints.push(equality_or_sat(
                Expression::Term(term1.clone()),
                Expression::Term(term2.clone()),
                multiplexer.clone(),
            ));
            if clause.explicits[i] {
                if let Term::Variable(v) = term2 {
                    definitions.insert(v, Expression::Term(term1));
                }
            } else {
                if let Term::Variable(v) = term1 {
                    definitions.insert(v, Expression::Term(term2));
                }
            }
        }
        for literal in &mut clause.body {
            match literal {
                Literal::Relation(RelOp::Eq, e1, e2) => {
                    *literal = equality_or_sat(
                        e1.clone(),
                        e2.clone(),
                        multiplexer.clone(),
                    );
                },
                _ => panic!("expected inlinee to only have equalities"),
            }
            
        }
    }
    Some(select_var)
}

/* Force each predicate literal in the clause to unify with at least one of the
 * heads of the clauses of the relation it refers to. Return false only if a
 * literal within the clause has no possible unification. */
fn bind_clause_variables(clause: &mut Clause, curr_var_id: &mut u32) -> bool {
    let mut clause_constraints = vec![];
    for (literal_pos, literal) in clause.body.iter_mut().enumerate() {
        if let Literal::Predicate(ref mut pred) = literal {
            if let Some(select_var) = bind_predicate_variables(
                pred,
                &mut clause_constraints,
                &mut clause.definitions,
                curr_var_id
            ) {
                clause.choice_points.insert(vec![literal_pos], select_var);
            } else {
                return false;
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
    for (query_pos, query) in target.queries.iter_mut().enumerate() {
        if let Some(select_var) = bind_predicate_variables(
            query,
            &mut target.body,
            &mut target.definitions,
            curr_var_id
        ) {
            target.choice_points.insert(vec![query_pos], select_var);
            for clause in &query.clauses {
                target.body.extend_from_slice(&clause.body);
                target.definitions.extend(clause.definitions.clone());
                for (mut path, select_var) in clause.choice_points.clone() {
                    path.insert(0, query_pos);
                    target.choice_points.insert(path, select_var);
                }
            }
        } else {
            target.body.push(Literal::Predicate(query.clone()));
        }
    }
    for clauses in target.assertions.values_mut() {
        clauses.retain_mut(|clause| bind_clause_variables(clause, curr_var_id));
    }
}

/* After the addition of multiplexer constraints, the clause bodies contained by
 * predicate literals are equivalent to the predicate literals themselves. So
 * just replace the predicate literals with these clause bodies. */
fn flatten_program_predicates(target: &mut Program) {
    for clauses in target.assertions.values_mut() {
        for clause in clauses {
            let mut new_body = vec![];
            for (literal_pos, literal) in clause.body.drain(..).enumerate() {
                match literal {
                    Literal::Predicate(p) => {
                        for mut iclause in p.clauses {
                            new_body.append(&mut iclause.body);
                            clause.definitions.extend(iclause.definitions.clone());
                            for (mut path, select_var) in iclause.choice_points.clone() {
                                path.insert(0, literal_pos);
                                target.choice_points.insert(path, select_var);
                            }
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
pub fn compile_program(base_program: &Program, depth: u32) -> (Program, Program) {
    let mut curr_var_id = 0;
    let mut base_program = base_program.clone();
    number_program_variables(&mut base_program, &mut curr_var_id);
    replace_program_nes(&mut base_program, &mut curr_var_id);
    build_explicit_defs(&mut base_program);
    record_explicit_definitions(&mut base_program);
    
    let mut current_program = base_program.clone();
    bottom_out_recursion(&mut current_program);

    for _i in 0..depth {
        let mut target_program = base_program.clone();
        number_program_variables(&mut target_program, &mut curr_var_id);
        record_explicit_definitions(&mut target_program);
        substitute_program(&mut target_program, current_program, &mut curr_var_id);
        bind_program_variables(&mut target_program, &mut curr_var_id);
        flatten_program_predicates(&mut target_program);
        flatten_program_expressions(&mut target_program, &mut curr_var_id);
        current_program = target_program;
    }

    //current_program.queries.clear();
    current_program.assertions.clear();
    (base_program, current_program)
}

/* Flatten the given expression down to a single term and place the definitions
 * of its parts into the given vector. The parts always take the following form:
 * term1 = -term2 or term1 = term2 OP term3 */
fn flatten_expression(
    out: Option<Term>,
    expr: &Expression,
    literals: &mut Vec<Literal>,
    definitions: &mut BTreeMap<Variable, Expression>,
    curr_var_id: &mut u32,
) -> Term {
    match expr {
        Expression::Term(t) => {
            if let Some(out) = out {
                literals.push(Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(out.clone()),
                    expr.clone(),
                ));
                if let Term::Variable(out_var) = &out {
                    definitions.insert(out_var.clone(), expr.clone());
                }
                out
            } else {
                t.clone()
            }
        },
        Expression::Negate(n) => {
            let out1_term = flatten_expression(None, n, literals, definitions, curr_var_id);
            let rhs = Expression::Negate(Box::new(Expression::Term(out1_term)));
            let out_var = Variable::new(*curr_var_id);
            *curr_var_id += 1;
            let out = out.unwrap_or(Term::Variable(out_var.clone()));
            if let Term::Variable(out_var) = &out {
                definitions.insert(out_var.clone(), rhs.clone());
            }
            literals.push(Literal::Relation(
                RelOp::Eq,
                Expression::Term(out.clone()),
                rhs,
            ));
            out
        },
        Expression::Binary(op, e1, e2) => {
            let out1_term = flatten_expression(None, e1, literals, definitions, curr_var_id);
            let out2_term = flatten_expression(None, e2, literals, definitions, curr_var_id);
            let rhs = Expression::Binary(
                op.clone(),
                Box::new(Expression::Term(out1_term)),
                Box::new(Expression::Term(out2_term)),
            );
            let out_var = Variable::new(*curr_var_id);
            *curr_var_id += 1;
            let out = out.unwrap_or(Term::Variable(out_var.clone()));
            if let Term::Variable(out_var) = &out {
                definitions.insert(out_var.clone(), rhs.clone());
            }
            literals.push(Literal::Relation(
                RelOp::Eq,
                Expression::Term(out.clone()),
                rhs,
            ));
            out
        }
    }
}

/* If the given literal contains expression trees, then produce an equivalent
 * literal that uses only one expression tree of height one. */
fn flatten_literal_expressions(
    literal: Literal,
    literals: &mut Vec<Literal>,
    definitions: &mut BTreeMap<Variable, Expression>,
    curr_var_id: &mut u32,
) {
    match literal.clone() {
        Literal::Relation(RelOp::Ne, _, _) =>
            unreachable!("not equal literals should not be present at this stage"),
        Literal::Predicate(_) => {
            literals.push(literal);
        },
        // If the given literal is already in three address from, then do not
        // try to flatten it again
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(_)),
            Expression::Term(_),
        ) => {
            literals.push(literal);
        },
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(_)),
            Expression::Negate(e),
        ) if matches!(&*e, Expression::Term(_)) => {
            literals.push(literal);
        },
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(_)),
            Expression::Binary(_, e1, e2),
        ) if matches!((&*e1, &*e2), (Expression::Term(_), Expression::Term(_))) => {
            literals.push(literal);
        },
        Literal::Relation(
            RelOp::Eq,
            e1,
            Expression::Term(Term::Constant(0)),
        ) => {
            flatten_expression(
                Some(Term::Constant(0)),
                &e1,
                literals,
                definitions,
                curr_var_id
            );
        },
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Constant(0)),
            e2,
        ) => {
            flatten_expression(
                Some(Term::Constant(0)),
                &e2,
                literals,
                definitions,
                curr_var_id
            );
        },
        // Literal is not in three address form, so flatten it
        Literal::Relation(RelOp::Eq, e1, e2) => {
            flatten_expression(
                Some(Term::Constant(0)),
                &binary_operation(
                    ArithOp::Minus,
                    e1.clone(),
                    e2.clone(),
                ),
                literals,
                definitions,
                curr_var_id
            );
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
        flatten_literal_expressions(
            literal.clone(),
            &mut expr_literals,
            &mut clause.definitions,
            curr_var_id,
        );
    }
    clause.body = expr_literals;
}

/* Flatten all expressions occuring in the program, creating additional clause
 * literals as necessary. */
fn flatten_program_expressions(
    program: &mut Program,
    curr_var_id: &mut u32,
) {
    let mut expr_literals = Vec::new();
    for literal in &mut program.body {
        flatten_literal_expressions(
            literal.clone(),
            &mut expr_literals,
            &mut program.definitions,
            curr_var_id
        );
    }
    program.body = expr_literals;
    for clauses in program.assertions.values_mut() {
        for clause in clauses {
            flatten_clause_expressions(clause, curr_var_id);
        }
    }
}

/* Collect a variable occuring in the given term, if possible. */
pub fn collect_term_variable(term: &Term, variables: &mut BTreeSet<Variable>) {
    if let Term::Variable(v) = term {
        variables.insert(v.clone());
    }
}

/* Collect all the variables occuring the given expression's terms. */
pub fn collect_expression_variables(expr: &Expression, variables: &mut BTreeSet<Variable>) {
    match expr {
        Expression::Term(t) => collect_term_variable(t, variables),
        Expression::Negate(n) => collect_expression_variables(n, variables),
        Expression::Binary(_op, e1, e2) => {
            collect_expression_variables(e1, variables);
            collect_expression_variables(e2, variables);
        }
    }
}

/* Collect all the variables occuring in the given predicate's terms. */
pub fn collect_predicate_variables(pred: &Predicate, variables: &mut BTreeSet<Variable>) {
    for term in &pred.terms {
        collect_term_variable(term, variables);
    }
}

/* Collect all the variables occuring in the given literal's terms. */
pub fn collect_literal_variables(literal: &Literal, variables: &mut BTreeSet<Variable>) {
    match literal {
        Literal::Predicate(p) => {
            collect_predicate_variables(p, variables);
        },
        Literal::Relation(_op, e1, e2) => {
            collect_expression_variables(e1, variables);
            collect_expression_variables(e2, variables);
        }
    }
}

/* Collect all the variables occuring in the given clause's head and body
 * literals. */
pub fn collect_clause_variables(clause: &Clause, variables: &mut BTreeSet<Variable>) {
    for term in &clause.head.terms {
        collect_term_variable(term, variables);
    }
    for literal in &clause.body {
        collect_literal_variables(literal, variables);
    }
}

/* Collect all the variables occuring in the given program's literals, clauses,
 * and queries. */
pub fn collect_program_variables(program: &Program, variables: &mut BTreeSet<Variable>) {
    for literal in &program.body {
        collect_literal_variables(literal, variables);
    }
    for clauses in program.assertions.values() {
        for clause in clauses {
            collect_clause_variables(&clause, variables);
        }
    }
    for query in &program.queries {
        for clause in &query.clauses {
            collect_clause_variables(&clause, variables);
        }
    }
}

/* Associates all the relations in a program with a graph node and adds an edge
 * between two relations a, b if a clause of a contains a predicate literal
 * referring to the relation b. */
pub fn graph_program_relations(program: &Program) -> Graph<(String, usize), ()> {
    let mut clause_graph = Graph::new();
    let mut node_map = HashMap::new();
    for signature in program.assertions.keys() {
        node_map.insert(signature, clause_graph.add_node(signature.clone()));
    }
    for (signature, clauses) in &program.assertions {
        for clause in clauses {
            for literal in &clause.body {
                if let Literal::Predicate(pred) = literal {
                    if node_map.contains_key(&pred.signature()) {
                        clause_graph.add_edge(
                            node_map[&signature],
                            node_map[&pred.signature()],
                            (),
                        );
                    }
                }
            }
        }
    }
    clause_graph
}

/* Determine whether every auxilliary variable in the program is explicitly
 * defined. This is necessary because searching for valid variable assignments
 * for implicitly defined variables can be too computationally expensive. */
pub fn build_explicit_defs(program: &mut Program) {
    // Analyze variable dependencies separately for each SCC of clauses. This is
    // in order to avoid repeatedly invalidating variable dependencies within an
    // SCC.
    let clause_graph = graph_program_relations(program);
    let sccs = tarjan_scc(&clause_graph);
    let mut explicit_params = BTreeMap::<Signature, Vec<bool>>::new();
    for scc in sccs {
        let mut curr_explicit_params = BTreeMap::new();
        for node in scc {
            let signature = clause_graph[node].clone();
            curr_explicit_params.insert(signature.clone(), vec![false; signature.1]);
            let clauses = program.assertions.get_mut(&signature).unwrap();
            let clauses_len = clauses.len();
            for clause in clauses.iter_mut() {
                let mut head_variables = BTreeSet::new();
                collect_predicate_variables(&clause.head, &mut head_variables);
                // Variables that are defined somewhere in the body
                let mut new_defined_vars = BTreeSet::new();
                // Variables we assume to be defined in the beginning
                let mut defined_vars = BTreeSet::new();
                collect_predicate_variables(&clause.head, &mut defined_vars);
                // Variables that are used in defining body variables
                let mut body_deps = BTreeSet::new();
                // Check that all variables are defined before use in the clause
                // body and also maintain data to determine which definitions we
                // can export.
                for literal in &clause.body {
                    match literal {
                        Literal::Relation(
                            RelOp::Eq,
                            Expression::Term(Term::Variable(v)),
                            e2,
                        ) => {
                            // In this case we have a definitions. So just make
                            // sure that all RHS variables are already defined.
                            let mut rhs_vars = BTreeSet::new();
                            collect_expression_variables(&e2, &mut rhs_vars);
                            if rhs_vars.is_subset(&defined_vars) {
                                new_defined_vars.insert(v.clone());
                                if !defined_vars.contains(&v) {
                                    defined_vars.insert(v.clone());
                                    if !head_variables.contains(&v) {
                                        body_deps.extend(rhs_vars);
                                    }
                                }
                            } else {
                                panic!("definition {:?} depends on undefined variables", literal);
                            }
                        },
                        Literal::Relation(_, e1, e2) => {
                            // In this case we just have a plain constraint. So
                            // just make sure all used variables are already
                            // defined
                            let mut vars = BTreeSet::new();
                            collect_expression_variables(&e1, &mut vars);
                            collect_expression_variables(&e2, &mut vars);
                            if !vars.is_subset(&defined_vars) {
                                panic!("constraint {:?} depends on undefined variables", literal);
                            }
                        },
                        Literal::Predicate(pred) => {
                            // If the definition of output variables in terms
                            // of inputs is set, then use this information
                            if let Some(explicits) = explicit_params.get(&pred.signature()) {
                                let mut new_defs = BTreeSet::new();
                                let mut implicit_vars = BTreeSet::new();
                                // Make sure that all implicit variables are
                                // already defined
                                for (i, is_explicit) in explicits.iter().enumerate() {
                                    if let Term::Variable(v) = &pred.terms[i] {
                                        if *is_explicit {
                                            new_defs.insert(v.clone());
                                        } else if !defined_vars.contains(v) {
                                            panic!("predicate literal {:?} depends on undefined variables", pred);
                                        } else {
                                            implicit_vars.insert(v.clone());
                                        }
                                    }
                                }
                                // Mark all variables in explicit positions as
                                // defined now
                                new_defined_vars.extend(new_defs.clone());
                                if !new_defs.is_subset(&defined_vars) {
                                    defined_vars.extend(new_defs.clone());
                                    if !new_defs.is_subset(&head_variables) {
                                        body_deps.extend(implicit_vars);
                                    }
                                }
                            } else {
                                // Otherwise be pessimistic and assume no
                                // explicit definitions
                                let mut vars = BTreeSet::new();
                                collect_predicate_variables(&pred, &mut vars);
                                if !vars.is_subset(&defined_vars) {
                                    panic!("predicate literal {:?} depends on undefined variables", pred);
                                }
                            }
                        }
                    }
                }

                // If there is more than one clause to this relation, then none
                // of its parameters can be explicitly defined
                if clauses_len > 1 {
                    clause.explicits = vec![false; signature.1];
                    continue;
                }
                // Head terms that are given an explicit definition in the body
                let defined_heads: BTreeSet<_> = head_variables
                    .intersection(&new_defined_vars)
                    .cloned()
                    .collect();
                // Head terms that in addition are not depended on by the body
                let explicit_params: BTreeSet<_> = defined_heads
                    .difference(&body_deps)
                    .cloned()
                    .collect();

                // Mark the explicit head variable positions so that future
                // strongly connected components need not explicitly define
                // arguments in the position corresponding to this parameter.
                let mut explicit_variables = vec![false; signature.1];
                for (i, term) in clause.head.terms.iter().enumerate() {
                    match term {
                        Term::Constant(_) => explicit_variables[i] = true,
                        Term::Variable(v) if explicit_params.contains(&v) => {
                            explicit_variables[i] = true;
                        },
                        _ => {}
                    }
                }
                curr_explicit_params.insert(signature.clone(), explicit_variables.clone());
                clause.explicits = explicit_variables;
            }
        }
        // Extending the explicit parameter map earlier could possibly
        // invalidate the analysis that determined a given predicate's
        // explicitness. So apply the analysis only for future SCCs.
        explicit_params.extend(curr_explicit_params);
    }
}

/* Record all of the definitions occuring in the program's clauses. */
fn record_explicit_definitions(program: &mut Program) {
    for clauses in program.assertions.values_mut() {
        for clause in clauses {
            for literal in &clause.body {
                if let Literal::Relation(
                    RelOp::Eq,
                    Expression::Term(Term::Variable(v)),
                    rhs,
                ) = literal {
                    clause.definitions.insert(v.clone(), rhs.clone());
                }
            }
        }
    }
}

/* Make a literal that computes the reciprocal of the given expression and
 * stores the result in a new variable. */
fn build_reciprocal_literal(
    expr: &Expression,
    curr_var_id: &mut u32,
) -> Literal {
    let new_var = Variable::new(*curr_var_id);
    let new_term = Expression::Term(Term::Variable(new_var.clone()));
    *curr_var_id += 1;
    Literal::Relation(
        RelOp::Eq,
        new_term,
        Expression::Binary(
            ArithOp::Divide,
            Box::new(Expression::Term(Term::Constant(1))),
            Box::new(expr.clone())
        ))
}

/* If the given literal is a not equal relation, then return an equality
 * relation that can only be solved if the difference has an inverse. */
fn convert_ne_literal(
    literal: Literal,
    curr_var_id: &mut u32,
) -> Literal {
    match literal {
        Literal::Relation(RelOp::Ne, lhs, Expression::Term(Term::Constant(0))) => {
            build_reciprocal_literal(&lhs, curr_var_id)
        },
        Literal::Relation(RelOp::Ne, Expression::Term(Term::Constant(0)), rhs) => {
            build_reciprocal_literal(&rhs, curr_var_id)
        },
        Literal::Relation(RelOp::Ne, lhs, rhs) => {
            build_reciprocal_literal(
                &binary_operation(ArithOp::Minus, lhs.clone(), rhs.clone()),
                curr_var_id,
            )
        },
        _ => literal,
    }
}

/* Replace all the not equal relations in the body with equality relations and
   divisions. */
fn replace_program_nes(program: &mut Program, curr_var_id: &mut u32) {
    for clauses in program.assertions.values_mut() {
        for clause in clauses {
            for literal in &mut clause.body {
                *literal = convert_ne_literal(
                    literal.clone(),
                    curr_var_id,
                );
            }
        }
    }
    for literal in &mut program.body {
        *literal = convert_ne_literal(
            literal.clone(),
            curr_var_id,
        );
    }
}
