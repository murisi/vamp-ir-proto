use pest::Parser;
use pest::iterators::Pair;
use std::collections::HashMap;
use std::fmt;

#[derive(Parser)]
#[grammar = "vamp_ir.pest"]
pub struct VampIRParser;

#[derive(Clone)]
pub struct Program {
    pub queries: Vec<Predicate>,
    pub assertions: HashMap<(String, usize), Vec<Clause>>,
}

impl Program {
    pub fn parse(unparsed_file: &str) -> Result<Self, pest::error::Error<Rule>> {
        let mut pairs = VampIRParser::parse(Rule::program, &unparsed_file)?;
        let mut queries = vec![];
        let mut assertions = HashMap::new();
        while let Some(pair) = pairs.next() {
            match pair.as_rule() {
                Rule::statement => {
                    let statement = Statement::parse(pair).expect("expected statement");
                    match statement {
                        Statement::Query(query) => queries.push(query),
                        Statement::Assertion(clause) => {
                            assertions.entry(clause.head.signature())
                                .or_insert_with(Vec::new)
                                .push(clause);
                        }
                    }
                },
                Rule::EOI => return Ok(Self { queries, assertions }),
                _ => unreachable!("program should either be statement or EOI")
            }
        }
        unreachable!("EOI should have been encountered")
    }
}

impl fmt::Debug for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for query in &self.queries {
            writeln!(f, "{:?}", query)?;
        }
        for clauses in self.assertions.values() {
            for clause in clauses {
                writeln!(f, "{:?}", clause)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assertion(Clause),
    Query(Predicate),
}

impl Statement {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::statement { return None }
        let pair = pair.into_inner().next()
            .expect("statement should not be empty");
        match pair.as_rule() {
            Rule::assertion => {
                let pair = pair.into_inner().next()
                    .expect("assertion should not be empty");
                Some(Self::Assertion(Clause::parse(pair)
                                     .expect("assertion should have exactly one clause")))
            },
            Rule::query => {
                let pair = pair.into_inner().next()
                    .expect("query should not be empty");
                Some(Self::Query(Predicate::parse(pair)
                                 .expect("query should have exactly one literal")))
            },
            _ => unreachable!("statement should either be assertion or query"),
        }
    }
}

#[derive(Clone)]
pub struct Clause {
    pub head: Predicate,
    pub body: Vec<Literal>,
}

impl Clause {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::clause { return None }
        let mut pairs = pair.into_inner();
        Some(Self {
            head: Predicate::parse(
                pairs.next().expect("clause should start with predicate")
            ).expect("clause head should be a predicate"),
            body: if let Some(pair) = pairs.next() {
                pair.into_inner().map(Literal::parse).collect::<Option<Vec<_>>>()
                    .expect("clause body should be sequence of literals")
            } else {
                vec![]
            },
        })
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.head)?;
        if self.body.is_empty() {
            write!(f, ".")?;
        } else {
            write!(f, " :-\n    {:?}", self.body[0])?;
            for literal in self.body[1..].iter() {
                write!(f, ",\n    {:?}", literal)?;
            }
            write!(f, ".")?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub enum Literal {
    Predicate(Predicate),
    Relation(RelOp, Expression, Expression),
}

impl Literal {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::literal { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("literal cannot be empty");
        match pair.as_rule() {
            Rule::predicate => {
                Some(Literal::Predicate(
                    Predicate::parse(pair).expect("literal should only contain predicate"),
                ))
            },
            Rule::expression => {
                let op = RelOp::parse(pairs.next().expect("expected relational operator"))
                    .expect("expected relational operator");
                let rhs_pair = pairs.next().expect("expected RHS expression");
                Some(Self::Relation(
                    op,
                    Expression::parse(pair)
                        .expect("equality literal should start with expression"),
                    Expression::parse(rhs_pair)
                        .expect("expected RHS to be a expression"),
                ))
            },
            _ => None,
        }
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Predicate(pred) => write!(f, "{:?}", pred),
            Self::Relation(op, expr1, expr2) => {
                write!(f, "{:?} {:?} {:?}", expr1, op, expr2)
            },
        }
    }
}

#[derive(Clone)]
pub enum RelOp { Eq, Ne }

impl RelOp {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::relOp { return None }
        match pair.as_span().as_str() {
            "=" => Some(Self::Eq),
            "!=" => Some(Self::Ne),
            _ => unreachable!("Encountered unknown relational operator")
        }
    }
}

impl fmt::Debug for RelOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Eq => write!(f, "="),
            Self::Ne => write!(f, "!="),
        }
    }
}

#[derive(Clone)]
pub struct Predicate {
    pub symbol: String,
    pub terms: Vec<Term>,
    pub clauses: Vec<Clause>,
}

impl Predicate {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::predicate { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("predicate should not be empty");
        if pair.as_rule() != Rule::predicate_sym {
            unreachable!("predicate should start with symbol")
        }
        Some(Self {
            symbol: pair.as_span().as_str().to_owned(),
            clauses: vec![],
            terms: if let Some(pair) = pairs.next() {
                pair.into_inner().map(Term::parse).collect::<Option<Vec<_>>>()
                    .expect("literal body should be a sequence of terms")
            } else {
                vec![]
            },
        })
    }
    pub fn signature(&self) -> (String, usize) {
        (self.symbol.clone(), self.terms.len())
    }
}

impl fmt::Debug for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.symbol)?;
        let mut iter = self.terms.iter();
        if let Some(term) = iter.next() {
            write!(f, "{:?}", term)?;
        }
        for term in iter {
            write!(f, ", {:?}", term)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Term {
    Variable(Variable),
    Constant(i32),
}

impl Term {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::term { return None }
        let pair = pair.into_inner().next().expect("term should not be empty");
        match pair.as_rule() {
            Rule::variable => {
                Some(Self::Variable(Variable::parse(pair).expect("term should be a variable")))
            },
            Rule::constant => {
                Some(Self::Constant(
                    pair.as_span().as_str().parse().ok().expect("constant should be an integer")
                ))
            },
            _ => None,
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Variable(v) => write!(f, "{:?}", v),
            Self::Constant(c) => write!(f, "{:?}", c),
        }
    }
}

#[derive(Clone, Eq, Ord)]
pub struct Variable {
    pub name: Option<String>,
    pub id: u32,
}

impl Variable {
    pub fn new(id: u32) -> Self {
        Self { id, name: None }
    }
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::variable { return None }
        Some(Variable {
            name: Some(pair.as_span().as_str().to_owned()),
            id: 0,
        })
    }
}

impl PartialEq for Variable {
    fn eq(&self, rhs: &Self) -> bool {
        self.id == rhs.id
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        self.id.partial_cmp(&rhs.id)
    }
}

impl fmt::Debug for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = &self.name {
            write!(f, "{}", name)?;
        }
        write!(f, "[{:?}]", self.id)?;
        Ok(())
    }
}

#[derive(Clone)]
pub enum Expression {
    Term(Term),
    Negate(Box<Expression>),
    Binary(ArithOp, Box<Expression>, Box<Expression>),
}

impl Expression {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::expression { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("expression should not be empty");
        let mut expr =
            Self::parse_product(pair).expect("expression should start with product");
        while let Some(pair) = pairs.next() {
            let op = ArithOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS product");
            let rhs = Self::parse_product(rhs_pair)
                .expect("expected RHS to be a product");
            expr = Self::Binary(op, Box::new(expr), Box::new(rhs));
        }
        Some(expr)
    }

    fn parse_product(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::product { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("product should not be empty");
        let mut product =
            Self::parse_value(pair).expect("product should start with value");
        while let Some(pair) = pairs.next() {
            let op = ArithOp::parse(pair).expect("expected arithmetic operator");
            let rhs_pair = pairs.next().expect("expected RHS value");
            let rhs = Self::parse_value(rhs_pair)
                .expect("expected RHS to be a value");
            product = Self::Binary(op, Box::new(product), Box::new(rhs));
        }
        Some(product)
    }

    fn parse_value(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::value { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("value should not be empty");
        match pair.as_rule() {
            Rule::term => Term::parse(pair).map(Expression::Term),
            Rule::expression => Self::parse(pair),
            Rule::negate => {
                let pair =
                    pairs.next().expect("negation operator should be followed by expression");
                Expression::parse(pair).map(|x| Expression::Negate(Box::new(x)))
            },
            _ => unreachable!("value should either be negation, term, or expression"),
        }
    }
}

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Term(t) => write!(f, "{:?}", t),
            Self::Negate(e) => write!(f, "-{:?}", e),
            Self::Binary(op, e1, e2) => write!(f, "({:?}{:?}{:?})", e1, op, e2),
        }
    }
}

#[derive(Clone)]
pub enum ArithOp { Times, Divide, Plus, Minus }

impl ArithOp {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() == Rule::plus_minus {
            match pair.as_span().as_str() {
                "+" => Some(Self::Plus),
                "-" => Some(Self::Minus),
                _ => unreachable!("Encountered unexpected arithmetic operator")
            }
        } else if pair.as_rule() == Rule::times_divide {
            match pair.as_span().as_str() {
                "*" => Some(Self::Times),
                "/" => Some(Self::Divide),
                _ => unreachable!("Encountered unexpected arithmetic operator")
            }
        } else {
            None
        }
    }
}

impl fmt::Debug for ArithOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Times => write!(f, "*"),
            Self::Divide => write!(f, "/"),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
        }
    }
}
