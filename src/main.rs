extern crate pest;
#[macro_use]
extern crate pest_derive;
use pest::Parser;
use pest::iterators::Pair;
use std::fs;

#[derive(Parser)]
#[grammar = "vamp_ir.pest"]
pub struct VampIRParser;

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Statement>,
}

impl Program {
    pub fn parse(unparsed_file: &str) -> Result<Self, pest::error::Error<Rule>> {
        let mut pairs = VampIRParser::parse(Rule::program, &unparsed_file)?;
        let mut statements = vec![];
        while let Some(pair) = pairs.next() {
            match pair.as_rule() {
                Rule::statement => {
                    statements.push(Statement::parse(pair).expect("expected statement"))
                },
                Rule::EOI => return Ok(Self { statements }),
                _ => unreachable!("program should either be statement or EOI")
            }
        }
        unreachable!("EOI should have been encountered")
    }
}

#[derive(Debug)]
pub enum Statement {
    Assertion(Clause),
    Query(Literal),
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
                Some(Self::Query(Literal::parse(pair)
                                 .expect("query should have exactly one literal")))
            },
            _ => unreachable!("statement should either be assertion or query"),
        }
    }
}

#[derive(Debug)]
pub struct Clause {
    pub head: Literal,
    pub body: Vec<Literal>,
}

impl Clause {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::clause { return None }
        let mut pairs = pair.into_inner();
        Some(Self {
            head: Literal::parse(
                pairs.next().expect("clause should have at least one literal")
            ).expect("clause head should be a literal"),
            body: if let Some(pair) = pairs.next() {
                pair.into_inner().map(Literal::parse).collect::<Option<Vec<_>>>()
                    .expect("clause body should be sequence of literals")
            } else {
                vec![]
            },
        })
    }
}

#[derive(Debug)]
pub enum Literal {
    Predicate(String, Vec<Term>),
    Eq(Term, Term),
    Neq(Term, Term),
}

impl Literal {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::literal { return None }
        let mut pairs = pair.into_inner();
        let pair = pairs.next().expect("literal cannot be empty");
        match pair.as_rule() {
            Rule::predicate_sym => {
                Some(Literal::Predicate(
                    pair.as_span().as_str().to_owned(),
                    if let Some(pair) = pairs.next() {
                        pair.into_inner().map(Term::parse).collect::<Option<Vec<_>>>()
                            .expect("literal body should be a sequence of terms")
                    } else {
                        vec![]
                    },
                ))
            },
            Rule::term => {
                match pairs.next().expect("expected relational operator").as_span().as_str() {
                    "=" => {
                        let rhs_pair = pairs.next().expect("expected RHS term");
                        Some(Self::Eq(
                            Term::parse(pair)
                                .expect("equality literal should start with term"),
                            Term::parse(rhs_pair).expect("expected RHS to be a term"),
                        ))
                    }, "!=" => {
                        let rhs_pair = pairs.next().expect("expected RHS term");
                        Some(Self::Neq(
                            Term::parse(pair)
                                .expect("inequality literal should start with term"),
                            Term::parse(rhs_pair).expect("expected RHS to be a term"),
                        ))
                    }, _ => None,
                }
            },
            _ => None,
        }
    }
}

#[derive(Debug)]
pub enum Term {
    Variable(String),
    Constant(i32),
}

impl Term {
    pub fn parse(pair: Pair<Rule>) -> Option<Self> {
        if pair.as_rule() != Rule::term { return None }
        let pair = pair.into_inner().next().expect("term should not be empty");
        match pair.as_rule() {
            Rule::variable => {
                Some(Self::Variable(pair.as_span().as_str().to_owned()))
            },
            Rule::constant => {
                Some(Self::Constant(pair.as_span().as_str().parse().ok()
                    .expect("constant should be an integer")))
            },
            _ => None,
        }
    }
}

fn main() {
    let unparsed_file = fs::read_to_string("tests/transitive.pir").expect("cannot read file");
    println!("{:?}", Program::parse(&unparsed_file));
}
