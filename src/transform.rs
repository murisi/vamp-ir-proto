use std::collections::{BTreeSet, HashMap, BTreeMap, VecDeque, HashSet};
use petgraph::{Graph, Direction};
use petgraph::prelude::Bfs;
use petgraph::visit::{Visitable, GraphRef, VisitMap};
use petgraph::algo::{tarjan_scc, is_cyclic_directed};
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

/* Force the given predicate literal to unify with at least one of the heads of
 * the clauses of the relation it refers to. Return false only if this predicate
 * has no possible unification. */
fn bind_predicate_variables(
    pred: &Predicate,
    constraints: &mut Vec<Literal>,
    curr_var_id: &mut u32
) -> bool {
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
            constraints.push(equality_or_sat(
                Expression::Term(term1),
                Expression::Term(term2),
                multiplexer.clone(),
            ));
        }
    }
    true
}

/* Force each predicate literal in the clause to unify with at least one of the
 * heads of the clauses of the relation it refers to. Return false only if a
 * literal within the clause has no possible unification. */
fn bind_clause_variables(clause: &mut Clause, curr_var_id: &mut u32) -> bool {
    let mut clause_constraints = vec![];
    for literal in &clause.body {
        if let Literal::Predicate(pred) = literal {
            if !bind_predicate_variables(pred, &mut clause_constraints, curr_var_id) {
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
    for query in &target.queries {
        if bind_predicate_variables(query, &mut target.literals, curr_var_id) {
            for clause in &query.clauses {
                target.literals.extend_from_slice(&clause.body);
            }
        } else {
            target.literals.push(Literal::Predicate(query.clone()));
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
pub fn iterate_program(base_program: &Program, pow: u32) -> Program {
    let mut curr_var_id = 0;
    let mut current_program = base_program.clone();
    number_program_variables(&mut current_program, &mut curr_var_id);
    build_explicit_defs(&current_program);
    bottom_out_recursion(&mut current_program);

    for _i in 1..pow {
        let mut target_program = base_program.clone();
        number_program_variables(&mut target_program, &mut curr_var_id);
        substitute_program(&mut target_program, current_program, &mut curr_var_id);
        bind_program_variables(&mut target_program, &mut curr_var_id);
        flatten_program_predicates(&mut target_program);
        flatten_program_expressions(&mut target_program, &mut curr_var_id);
        current_program = target_program;
    }

    current_program.queries.clear();
    current_program.assertions.clear();
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
            Expression::Term(Term::Variable(_)),
            Expression::Term(_),
        ) => literal,
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(_)),
            Expression::Negate(e),
        ) if matches!(&*e, Expression::Term(_)) => literal,
        Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(_)),
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
    let mut expr_literals = Vec::new();
    for literal in &mut program.literals {
        *literal = flatten_literal_expressions(
            literal.clone(),
            &mut expr_literals,
            curr_var_id
        );
    }
    program.literals.append(&mut expr_literals);
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
    for literal in &program.literals {
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
pub fn graph_program_relations(program: &Program) -> Graph<&(String, usize), ()> {
    let mut clause_graph = Graph::new();
    let mut node_map = HashMap::new();
    for signature in program.assertions.keys() {
        node_map.insert(signature, clause_graph.add_node(signature));
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

/* Associates all the variables in a clause with a graph node and adds an edge
 * between two variables a, b if there is a literal of the form a = f(b) where
 * f is some function. */
pub fn graph_clause_variables(clause: &Clause) -> (Graph<Variable, ()>, Variable) {
    let mut variable_graph = Graph::new();
    let mut node_map = BTreeMap::new();
    let constant_variable = Variable::new(u32::MAX);
    let mut clause_variables = BTreeSet::new();
    clause_variables.insert(constant_variable.clone());
    collect_clause_variables(clause, &mut clause_variables);
    for variable in clause_variables {
        node_map.insert(variable.clone(), variable_graph.add_node(variable));
    }
    for literal in &clause.body {
        if let Literal::Relation(
            RelOp::Eq,
            Expression::Term(Term::Variable(v)),
            rhs,
        ) = literal {
            let mut expression_variables = BTreeSet::new();
            expression_variables.insert(constant_variable.clone());
            collect_expression_variables(rhs, &mut expression_variables);
            for vd in expression_variables {
                variable_graph.add_edge(
                    node_map[&v],
                    node_map[&vd],
                    (),
                );
            }
        }
    }
    (variable_graph, constant_variable)
}

/// Create a new **Bfs**, using the graph's visitor map, and put **starts**
/// in the stack of nodes to visit.
pub fn new_bfs<N, VM, G>(graph: G, starts: HashSet<N>) -> Bfs<N, VM>
where
    G: GraphRef + Visitable<NodeId = N, Map = VM>,
    VM: VisitMap<N>,
    N: Copy + PartialEq,
    
{
    let mut discovered = graph.visit_map();
    let mut stack = VecDeque::new();
    for elt in starts {
        discovered.visit(elt);
        stack.push_front(elt);
    }
    Bfs { stack, discovered }
}

/* Determine whether every auxilliary variable in the program is explicitly
 * defined. This is necessary because searching for valid variable assignments
 * for implicitly defined variables can be too computationally expensive. */
pub fn build_explicit_defs(program: &Program) {
    // Analyze variable dependencies separately for each SCC of clauses. This is
    // in order to avoid repeatedly invalidating variable dependencies within an
    // SCC.
    let clause_graph = graph_program_relations(program);
    let sccs = tarjan_scc(&clause_graph);
    let mut explicit_params = BTreeMap::<&Signature, Vec<bool>>::new();
    for scc in sccs {
        let mut curr_explicit_params = BTreeMap::new();
        for node in scc {
            let signature = clause_graph[node];
            curr_explicit_params.insert(signature, vec![false; signature.1]);
            let clauses = &program.assertions[signature];
            for clause in clauses {
                // Graph the dependencies between variables in this clause in
                // order to determine how auxilliary variable witnesses can be
                // derived.
                let (variable_graph, constant) = graph_clause_variables(clause);
                if is_cyclic_directed(&variable_graph) {
                    panic!("cyclic explicit variable definitions found");
                }

                // To facilitate reverse variable lookups
                let mut node_map = BTreeMap::new();
                for ix in variable_graph.node_indices() {
                    node_map.insert(variable_graph[ix].clone(), ix);
                }

                // Obtain head, clause, and body variable indicies from the
                // variable graph constructed above.
                let mut head_variables = BTreeSet::new();
                collect_predicate_variables(&clause.head, &mut head_variables);
                let head_variable_ixs: HashSet<_> =
                    head_variables.into_iter().map(|n| node_map[&n]).collect();
                let mut clause_variables = BTreeSet::new();
                collect_clause_variables(clause, &mut clause_variables);
                let clause_variable_ixs: HashSet<_> =
                    clause_variables.into_iter().map(|n| node_map[&n]).collect();
                let body_variable_ixs: HashSet<_> =
                    clause_variable_ixs.difference(&head_variable_ixs).cloned().collect();

                // Collect a set of variables such that all expressions defined
                // in terms of them can be explicitly defined by the compiler.
                // These variables are those either head variables or are
                // explicitly defined by a predicate used in the body.
                let mut valid_leafs = HashSet::new();
                valid_leafs.extend(head_variable_ixs.clone());
                valid_leafs.insert(node_map[&constant]);
                for literal in &clause.body {
                    if let Literal::Predicate(pred) = literal {
                        if let Some(explicits) = explicit_params.get(&pred.signature()) {
                            for (i, is_explicit) in explicits.iter().enumerate() {
                                if *is_explicit {
                                    if let Term::Variable(v) = &pred.terms[i] {
                                        valid_leafs.insert(node_map[&v]);
                                    }
                                }
                            }
                        }
                    }
                }

                // Ensure that the leafs of our variable DAG come from the set
                // defined above.
                for ix in variable_graph.node_indices() {
                    match variable_graph.edges_directed(ix, Direction::Outgoing).next() {
                        None if !valid_leafs.contains(&ix) =>
                            panic!("all variables must be explicitly defined \
                                    from head variables"),
                        _ => {}
                    }
                }

                // If there is more than one clause to this relation, then none
                // of its parameters can be explicitly defined
                if clauses.len() > 1 { continue }

                // Determine variables depended on by body variables
                let mut bfs = new_bfs(&variable_graph, body_variable_ixs);
                let mut body_dependencies = HashSet::new();
                while let Some(nx) = bfs.next(&variable_graph) {
                    body_dependencies.insert(nx);
                }
                
                // Determine the explicitly defined head variables that are not
                // depended on by the body
                let free_variables: HashSet<_> =
                    head_variable_ixs.difference(&body_dependencies).cloned().collect();
                let mut explicit_params = HashSet::new();
                for var in free_variables {
                    if let Some(_) =
                        variable_graph.edges_directed(var, Direction::Outgoing).next() {
                            explicit_params.insert(var);
                    }
                }

                // Mark the explicit head variable positions so that future
                // strongly connected components need not explicitly define
                // arguments in the position corresponding to this parameter.
                let mut explicit_variables = vec![false; signature.1];
                for (i, term) in clause.head.terms.iter().enumerate() {
                    match term {
                        Term::Constant(_) => explicit_variables[i] = true,
                        Term::Variable(v) if explicit_params.contains(&node_map[v]) => {
                            explicit_variables[i] = true;
                        },
                        _ => {}
                    }
                }
                curr_explicit_params.insert(signature, explicit_variables);
            }
        }
        // Extending the explicit parameter map earlier could possibly
        // invalidate the analysis that determined a given predicate's
        // explicitness. So apply the analysis only for future SCCs.
        explicit_params.extend(curr_explicit_params);
    }
}
