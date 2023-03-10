/* ========================================================================== */
/*                                CSP Variable                                */
/* ========================================================================== */

use std::{collections::HashMap, fmt::Display};

use anyhow::{bail, Result};
use aries::core::INT_CST_MAX;
use aries::model::lang::expr::{and, geq, lt, or};
use aries::model::Model;
use aries::solver::Solver;
use malachite::Rational;

/// Represents a variable in a CSP problem.
#[derive(Clone, PartialEq, Eq)]
pub struct CspVariable {
    domain: Vec<Rational>,
}

impl CspVariable {
    pub fn new(domain: Vec<Rational>) -> Self {
        Self { domain }
    }
}

impl Display for CspVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut domain = self.domain.clone();
        domain.sort();
        f.write_fmt(format_args!(
            "{{{}}}",
            domain.iter().map(|v| format!("{v}")).collect::<Vec<_>>().join(", ")
        ))
    }
}

/* ========================================================================== */
/*                               CSP Constraint                               */
/* ========================================================================== */

/// Represents the term of a constraint in a CSP problem.
pub struct CspConstraintTerm {
    id: String,
    delay: Rational,
}

impl CspConstraintTerm {
    pub fn new_delayed(id: String, delay: Rational) -> Self {
        Self { id, delay }
    }

    pub fn new(id: String) -> Self {
        Self { id, delay: 0.into() }
    }
}

/// Represents a constraint in a CSP problem.
pub enum CspConstraint {
    Lt(CspConstraintTerm, CspConstraintTerm),     // a < b
    Le(CspConstraintTerm, CspConstraintTerm),     // a <= b
    Equals(CspConstraintTerm, CspConstraintTerm), // a == b
    Not(Box<CspConstraint>),                      // not (a)
    Or(Vec<CspConstraint>),                       // a1 or a2 or ... or an
}

impl Display for CspConstraintTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}", self.id))?;
        if self.delay != 0 {
            let s = if self.delay < 0 { "-" } else { "+" };
            f.write_fmt(format_args!(" {} {}", s, self.delay))?;
        }
        Ok(())
    }
}

impl Display for CspConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CspConstraint::Lt(a, b) => f.write_fmt(format_args!("{a} <  {b}")),
            CspConstraint::Le(a, b) => f.write_fmt(format_args!("{a} <= {b}")),
            CspConstraint::Equals(a, b) => f.write_fmt(format_args!("{a} == {b}")),
            CspConstraint::Not(a) => f.write_fmt(format_args!("not ({a})")),
            CspConstraint::Or(a) => f.write_fmt(format_args!(
                "{}",
                a.iter().map(|c| format!("({c})")).collect::<Vec<_>>().join(" or ")
            )),
        }
    }
}

/* ========================================================================== */
/*                                 CSP Problem                                */
/* ========================================================================== */

/// Represents a CSP problem.
#[derive(Default)]
pub struct CspProblem {
    variables: HashMap<String, CspVariable>,
    constraints: Vec<CspConstraint>,
}

impl CspProblem {
    /// Appends a new variable in the problem.
    pub fn add_variable(&mut self, id: String, variable: CspVariable) -> Result<()> {
        if self.variables.contains_key(&id) {
            if self.variables.get(&id).unwrap() != &variable {
                bail!(format!("The variable {id} is already assigned with another value"));
            } // Else, the values are the same so we ignore it.
        } else {
            self.variables.entry(id).or_insert(variable);
        }
        Ok(())
    }

    /// Appends a new constraint in the problem.
    pub fn add_constraint(&mut self, constraint: CspConstraint) {
        self.constraints.push(constraint);
    }

    /// Returns the formatted id for a start variable.
    pub fn start_id(id: &String) -> String {
        format!("{id}::start")
    }

    /// Returns the formatted id for an end variable.
    pub fn end_id(id: &String) -> String {
        format!("{id}::end")
    }

    fn is_valid(&self) -> bool {
        let mut m: Model<String> = Model::new();

        let mut vars = HashMap::new();

        for (name, domain) in self.variables.iter() {
            let domain: Vec<(i32, i32)> = Vec::new(); // plage possible pour cette variable
            let var = m.new_ivar(0, INT_CST_MAX, name.clone());
            vars.insert(name.clone(), var);

            let mut options = Vec::new();
            for (lb, ub) in domain {
                let lb = m.reify(geq(var, lb));
                let ub = m.reify(lt(var, ub));
                let in_interval = m.reify(and([lb, ub]));
                options.push(in_interval);
            }
            m.enforce(or(options), []);
        }

        let t = |x: &CspConstraintTerm| {
            let var = vars[&x.id];
            var + 4 // TODO: translate rational add
        };

        for c in &self.constraints {
            match c {
                CspConstraint::Lt(lhs, rhs) => m.enforce(lt(t(lhs), t(rhs)), []),
                CspConstraint::Le(_, _) => {}
                CspConstraint::Equals(_, _) => {}
                CspConstraint::Not(_) => {}
                CspConstraint::Or(_) => {}
            }
        }

        let mut solver = Solver::new(m);
        let result = solver.solve().expect("Solver interrupted (by whomm ???)");

        result.is_some() // an assignment exists
    }
}

impl Display for CspProblem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("\n========== CSP ==========\n")?;
        f.write_str("Variables:\n")?;
        for (id, var) in self.variables.iter() {
            f.write_fmt(format_args!("    {} in {}\n", id, var))?;
        }
        f.write_str("\nConstraints:\n")?;
        for constraint in self.constraints.iter() {
            f.write_fmt(format_args!("    {constraint}\n"))?;
        }
        f.write_str("=========================\n")
    }
}
