use crate::Strat::{Activity, Forward};
use aries_core::{Lit, INT_CST_MAX};
use aries_model::extensions::{SavedAssignment, Shaped};
use aries_model::lang::{FAtom, SAtom, Type, Variable};
use aries_model::symbols::SymbolTable;
use aries_model::types::TypeHierarchy;
use aries_planners::encode::{encode, populate_with_task_network};
use aries_planners::fmt::{format_hddl_plan, format_pddl_plan};
use aries_planners::forward_search::ForwardSearcher;
use aries_planners::Solver;
use aries_planning::chronicles::analysis::hierarchical_is_non_recursive;
use aries_planning::chronicles::constraints::Constraint;
use aries_planning::chronicles::{
    Chronicle, ChronicleInstance, ChronicleKind, ChronicleOrigin, ChronicleTemplate, Condition, Container, Ctx, Effect,
    FiniteProblem, Problem, StateFun, SubTask, VarType, TIME_SCALE,
};
use aries_tnet::theory::{StnConfig, StnTheory, TheoryPropagationLevel};
use aries_utils::input::Sym;
use pyo3::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::str::FromStr;
use std::sync::Arc;
use std::time::Instant;

/// Top PDDL types
static TASK_TYPE: &str = "★task★";
static ABSTRACT_TASK_TYPE: &str = "★abstract_task★";
static ACTION_TYPE: &str = "★action★";
static DURATIVE_ACTION_TYPE: &str = "★durative-action★";
static METHOD_TYPE: &str = "★method★";
static PREDICATE_TYPE: &str = "★predicate★";
static OBJECT_TYPE: &str = "★object★";
static FUNCTION_TYPE: &str = "★function★";

/// Custom types
type Symbol = String;
/// It is composed of the name followed by the arguments.
/// An argument is of the form "name - type"
type Sign = Vec<Symbol>;
/// It is composed of the name followed by the arguments followed by the temporal interval.
type TempSign = Vec<String>;
/// It is composed of the name followed by the arguments followed by a value and finally the temporal interval.
type TempValSign = Vec<String>;
/// It is composed of the first element, the relation, and the second element.
type Constr = Vec<String>;
/// It is a specific type of `Constr`.
/// The format of a temporal constraint is `[label1_(start|end) + delay1, relation, label2_(start|end) + delay2]` with:
///     - timepoint1 + delay: the first timepoint of the constraint,and its delay.
///     - relation: must be one of the following "==", "<", ">", "<=", ">=".
///     - timepoint2 + delay: the second timepoint of the constraint,and its delay.
type TemporalConstraint = Vec<String>;
/// It is composed of the signature of the associated state variable followed by its value and finally the temporal interval.
type Cond = TempValSign;
/// It is composed of the signature of the associated state variable followed by its value and finally the temporal interval.
type Eff = TempValSign;

/// A python class to generate a planning problem with chronicles.
#[pyclass]
struct ChronicleProblem {
    types: Vec<(Sym, Option<Sym>)>, // Type symbol with its optional parent type symbol
    constants: HashMap<Sym, bool>,  // Map a symbol to a boolean representing if the symbol is a constant
    symbols: Vec<(Sym, Sym)>,       // Symbol with its type symbol
    symbol_table: Option<SymbolTable>,
    state_variables: Vec<StateFun>,
    context: Option<Ctx>,
    init_ch: Option<Chronicle>,
    templates: Vec<ChronicleTemplate>,
}

/// Public methods of ChronicleProblem
#[pymethods]
impl ChronicleProblem {
    /// Constructor of the class.
    #[new]
    fn new() -> Self {
        ChronicleProblem {
            types: vec![
                (TASK_TYPE.into(), None),
                (ABSTRACT_TASK_TYPE.into(), Some(TASK_TYPE.into())),
                (ACTION_TYPE.into(), Some(TASK_TYPE.into())),
                (DURATIVE_ACTION_TYPE.into(), Some(TASK_TYPE.into())),
                (METHOD_TYPE.into(), None),
                (PREDICATE_TYPE.into(), None),
                (FUNCTION_TYPE.into(), None),
                (OBJECT_TYPE.into(), None),
            ],
            constants: HashMap::new(),
            symbols: vec![],
            symbol_table: None,
            state_variables: vec![],
            context: None,
            init_ch: None,
            templates: vec![],
        }
    }

    /// Allows the user to add their own hierarchical types.
    fn add_type(&mut self, sym: Symbol, parent: Option<Symbol>) {
        if let Some(parent) = parent {
            self.types.push((sym.into(), Some(parent.into())));
        } else {
            self.types.push((sym.into(), Some(OBJECT_TYPE.into())));
        }
    }

    /// Allows the user to add the symbol of a constant with its type.
    fn add_constant_symbol(&mut self, sym: Symbol, tpe: Symbol) {
        self.symbols.push((sym.clone().into(), tpe.into()));
        self.constants.insert(sym.into(), true);
    }

    /// Allows the user to add the symbol of a predicate.
    fn add_predicate_symbol(&mut self, sym: Symbol) {
        self.symbols.push((sym.clone().into(), PREDICATE_TYPE.into()));
        self.constants.insert(sym.into(), false);
    }

    /// Allows the user to add the symbol of a function.
    fn add_function_symbol(&mut self, sym: Symbol) {
        self.symbols.push((sym.clone().into(), FUNCTION_TYPE.into()));
        self.constants.insert(sym.into(), false);
    }

    /// Allows the user to add the symbol of an action.
    fn add_action_symbol(&mut self, sym: Symbol) {
        self.symbols.push((sym.clone().into(), ACTION_TYPE.into()));
        self.constants.insert(sym.into(), false);
    }

    /// Allows the user to add the symbol of a task.
    fn add_task_symbol(&mut self, sym: Symbol) {
        self.symbols.push((sym.clone().into(), ABSTRACT_TASK_TYPE.into()));
        self.constants.insert(sym.into(), false);
    }

    /// Allows the user to add the symbol of a method.
    fn add_method_symbol(&mut self, sym: Symbol) {
        self.symbols.push((sym.clone().into(), METHOD_TYPE.into()));
        self.constants.insert(sym.into(), false);
    }

    /// Creates the symbol table used for the creation of the state variables and the context.
    /// Must be called when all symbols have been created.
    fn create_symbol_table(&mut self) {
        self.symbol_table =
            Some(SymbolTable::new(TypeHierarchy::new(self.types.to_vec()).unwrap(), self.symbols.to_vec()).unwrap());
    }

    /// Allows the user to add a predicate with its signature.
    fn add_predicate(&mut self, sign: Sign) {
        self.add_state_variable(sign, Type::Bool);
    }

    /// Allows the user to add a function with its signature.
    fn add_function(&mut self, sign: Sign) {
        self.add_state_variable(sign, Type::Int);
    }

    /// Creates the context of the problem and the initial chronicle.
    /// Must be called when all state variables (i.e. predicates and functions) have been created.
    fn create_context(&mut self) {
        self.context = Some(Ctx::new(
            Arc::new(self.symbol_table.as_ref().unwrap().clone()),
            self.state_variables.to_vec(),
        ));
        self.init_ch = Some(Chronicle {
            kind: ChronicleKind::Problem,
            presence: Lit::TRUE,
            start: self.context.as_ref().unwrap().origin(),
            end: self.context.as_ref().unwrap().horizon(),
            name: vec![],
            task: None,
            conditions: vec![],
            effects: vec![],
            constraints: vec![],
            subtasks: vec![],
        });
    }

    /// Allow the user to add the initial task network goal, describing the goal.
    ///
    /// Parameters
    /// ----------
    /// - tasks : list of TempSign
    ///     - List of task temporal signatures of the initial task network.
    /// - constraints : list of TemporalConstraint
    ///     - List of temporal constraints between the tasks of the initial task network.
    fn add_goal(&mut self, tasks: Vec<TempSign>, constraints: Vec<TemporalConstraint>) {
        add_task_network(
            Container::Instance(0),
            self.init_ch.as_mut().unwrap(),
            self.context.as_mut().unwrap(),
            None,
            tasks,
            constraints,
        )
    }

    /// Allows the user to add an initial effect, describing a part of the initial state.
    ///
    /// Parameters
    /// ----------
    /// - effect: Eff
    ///     - The initial effect to add.
    fn add_initial_effect(&mut self, mut effect: Eff) {
        let sign_end: String = effect.pop().unwrap();
        let sign_end: Vec<&str> = sign_end.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
        let value_end: &str = sign_end[0];
        let sign_start: String = effect.pop().unwrap();
        let sign_start: Vec<&str> = sign_start.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
        let value_start: &str = sign_start[0];
        let value: bool = effect.pop().unwrap().to_lowercase().parse().unwrap();
        let sv = satom_from_signature(self.context.as_mut().unwrap(), effect);
        let ch = self.init_ch.as_mut().unwrap();

        let start = if value_start == "__start__" || value_start == "__now__" {
            ch.start
        } else if value_start == "__end__" {
            ch.end
        } else {
            panic!("unsupported start case {}", value_start)
        };

        let end = if value_end == "__end__" {
            ch.end
        } else if value_end == "__start__" || value_end == "__now__" {
            ch.start
        } else {
            panic!("unsupported end case {}", value_end)
        };

        ch.effects.push(Effect {
            transition_start: start,
            persistence_start: end,
            state_var: sv,
            value: value.into(),
        });
    }

    /// Allows the user to add an action.
    ///
    /// Parameters
    /// ----------
    /// - action : TempSign
    ///     - Signature of the action.
    /// - constraints : list of Constr
    ///     - List of generic and temporal constraints over the variables in the signature.
    /// - conditions : list of Cond
    ///     - List of preconditions of the action.
    /// - effects : list of Eff
    ///     - List of effects of the action.
    fn add_action(&mut self, action: TempSign, constraints: Vec<Constr>, conditions: Vec<Cond>, effects: Vec<Eff>) {
        self.add_template(action, constraints, conditions, effects, None, None, None);
    }

    /// Allows the user to add a method.
    ///
    /// Parameters
    /// ----------
    /// - method : TempSign
    ///     - Signature of the method.
    /// - constraints : list of Constr
    ///     - List of generic and temporal constraints over the variables in the signature.
    /// - conditions : list of Cond
    ///     - List of preconditions of the template.
    /// - task : TempSign
    ///     - Signature of the task achieved by the template.
    /// - subtasks : list of TempSign
    ///     - List of the requiered tasks in order to achieve the `task`.
    /// - subtasks_constraints : list of TemporalConstraint
    ///     - List of temporal constraint between the subtasks.
    fn add_method(
        &mut self,
        method: TempSign,
        constraints: Vec<Constr>,
        conditions: Vec<Cond>,
        task: TempSign,
        subtasks: Vec<TempSign>,
        subtasks_constraints: Vec<TemporalConstraint>,
    ) {
        self.add_template(
            method,
            constraints,
            conditions,
            vec![],
            Some(task),
            Some(subtasks),
            Some(subtasks_constraints),
        )
    }

    /// Final method to call. Solve the problem defined by this instance.
    ///
    /// Parameters
    /// ----------
    /// - output_file : str
    ///     - Path to the output file where the plan will be saved.
    fn solve(&self, output_file: &str) {
        println!("======= Chronicle =======");
        println!("{:?}", self.init_ch);
        println!("=========================");

        println!("======= Templates =======");
        for template in self.templates.to_vec() {
            println!("{:?}", template.chronicle);
            println!("==========");
        }
        println!("=========================");

        run_problem(
            &mut Problem {
                context: self.context.as_ref().unwrap().clone(),
                templates: self.templates.to_vec(),
                chronicles: vec![ChronicleInstance {
                    parameters: vec![],
                    origin: ChronicleOrigin::Original,
                    chronicle: self.init_ch.as_ref().unwrap().clone(),
                }],
            },
            output_file,
        );
    }
}

/// Private methods of ChronicleProblem.
impl ChronicleProblem {
    /// Generic method to create a state variable (i.e. predicate or function).
    ///
    /// Parameters
    /// ----------
    /// - sign : Sign
    ///     - The signature of the state variable.
    /// - return_type : Type
    ///     - The type of the state variable:
    ///         - Type::Bool for a predicate
    ///         - Type::Int for a function
    fn add_state_variable(&mut self, sign: Sign, return_type: Type) {
        let symbol_table = self.symbol_table.as_ref().unwrap();
        let sym = symbol_table.id(&sign[0]).unwrap();
        let mut tpe = vec![];
        for arg in sign.iter().skip(1) {
            // arg is of the form "value - type"
            let value_tpe: Vec<&str> = arg.split(" - ").collect();
            tpe.push(Type::Sym(symbol_table.types.id_of(value_tpe[1]).unwrap()));
        }
        tpe.push(return_type);
        self.state_variables.push(StateFun { sym, tpe });
    }

    /// Generic method to add a template (i.e. action or method).
    ///
    /// Parameters
    /// ----------
    /// - sign : Sign
    ///     - Signature of the template.
    /// - constraints : list of Constr
    ///     - List of generic and temporal constraints over the variables in the signature.
    /// - conditions : list of Cond
    ///     - List of preconditions of the template.
    /// - effects : list of Eff
    ///     - List of effects of the template.
    /// - task : Sign, optional
    ///     - Signature of the task achieved by the template.
    /// - subtasks : list of Sign, optional
    ///     - List of the requiered tasks in order to achieve the `task`.
    /// - subtasks_constraints : list of TemporalConstraint, optional
    ///     - List of temporal constraint between the subtasks.
    fn add_template(
        &mut self,
        mut sign: TempSign,
        constraints: Vec<Constr>,
        conditions: Vec<Cond>,
        effects: Vec<Eff>,
        task: Option<Sign>,
        subtasks: Option<Vec<TempSign>>,
        subtasks_constraints: Option<Vec<TemporalConstraint>>,
    ) {
        let context = self.context.as_mut().unwrap();
        let kind = if task.is_none() {
            ChronicleKind::Action
        } else {
            ChronicleKind::Method
        };
        let c = Container::Template(self.templates.len());
        let mut params: Vec<Variable> = vec![];
        let mut args: HashMap<&str, SAtom> = HashMap::new();

        // Presence
        let prez = context.model.new_bvar(c / VarType::Presence);
        params.push(prez.into());
        let prez = prez.true_lit();

        // Start & End from signature
        let ch_sign_end: String = sign.pop().unwrap();
        let ch_sign_end: Vec<&str> = ch_sign_end.split(" - ").collect::<Vec<&str>>()[0]
            .split(" + ")
            .collect();
        let ch_value_end: &str = ch_sign_end[0];
        let ch_delay_end: i32 = ch_sign_end[1].parse().unwrap();
        let ch_sign_start: String = sign.pop().unwrap();
        let ch_sign_start: Vec<&str> = ch_sign_start.split(" - ").collect::<Vec<&str>>()[0]
            .split(" + ")
            .collect();
        let ch_value_start: &str = ch_sign_start[0];
        let ch_delay_start: i32 = ch_sign_start[1].parse().unwrap();

        // Start & End of chronicle
        let start = context
            .model
            .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::ChronicleStart);
        params.push(start.into());
        let start = FAtom::from(start) + ch_delay_start;

        let end: FAtom = if ch_value_start == ch_value_end {
            start + FAtom::EPSILON
        } else {
            let end = context
                .model
                .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::ChronicleEnd);
            params.push(end.into());
            end.into()
        } + ch_delay_end;

        // Name & Parameters
        let mut name: Vec<SAtom> = vec![context
            .typed_sym(context.model.get_symbol_table().id(&sign[0]).unwrap())
            .into()];
        for arg in sign.iter().skip(1) {
            let sign_arg: Vec<&str> = arg.split(" - ").collect();
            let value_arg: &str = sign_arg[0];
            let type_arg: &str = sign_arg[1];
            let is_constant: bool = *self.constants.get(value_arg).unwrap_or(&false);
            if is_constant {
                let argument = context.typed_sym(context.model.get_symbol_table().id(value_arg).unwrap());
                args.insert(value_arg, argument.into());
                name.push(argument.into());
            } else {
                let var_type = context.model.get_symbol_table().types.id_of(type_arg).unwrap();
                let argument = context
                    .model
                    .new_optional_sym_var(var_type, prez, c / VarType::Parameter);
                args.insert(value_arg, argument.into());
                params.push(argument.into());
                name.push(argument.into());
            }
        }

        // Task
        let task: Vec<SAtom> = if let Some(task) = task {
            let mut tn: Vec<SAtom> = vec![context
                .typed_sym(context.model.get_symbol_table().id(&task[0]).unwrap())
                .into()];
            for arg in task.iter().skip(1) {
                let value_arg = arg.split(" - ").collect::<Vec<&str>>()[0];
                tn.push(*args.get(value_arg).unwrap());
            }
            tn
        } else {
            name.clone()
        };

        // Chronicle
        let mut ch = Chronicle {
            kind,
            presence: prez,
            start,
            end,
            name: name.clone(),
            task: Some(task),
            conditions: vec![],
            effects: vec![],
            constraints: vec![],
            subtasks: vec![],
        };

        // Effect
        for mut effect in effects {
            let sign_end: String = effect.pop().unwrap();
            let sign_end: Vec<&str> = sign_end.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
            let value_end: &str = sign_end[0];
            let delay_end: i32 = sign_end[1].parse().unwrap();
            let sign_start: String = effect.pop().unwrap();
            let sign_start: Vec<&str> = sign_start.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
            let value_start: &str = sign_start[0];
            let delay_start: i32 = sign_start[1].parse().unwrap();
            let value: bool = effect.pop().unwrap().to_lowercase().parse().unwrap();

            let mut sv: Vec<SAtom> = vec![context
                .typed_sym(context.model.get_symbol_table().id(&effect[0]).unwrap())
                .into()];
            for arg in effect.iter().skip(1) {
                let value_arg = arg.split(" - ").collect::<Vec<&str>>()[0];
                sv.push(*args.get(value_arg).unwrap());
            }

            let start = if value_start == "__start__" || value_start == "__now__" || value_start == ch_value_start {
                ch.start
            } else if value_start == "__end__" || value_start == ch_value_end {
                ch.end
            } else {
                panic!("unsupported start case: {}", value_start);
            };

            let end = if value_end == "__end__" || value_end == "__now__" || value_end == ch_value_end {
                ch.end
            } else if value_end == "__start__" || value_end == ch_value_start {
                ch.start + FAtom::EPSILON
            } else {
                panic!("unsupported end case: {}", value_end);
            };

            ch.effects.push(Effect {
                transition_start: start + delay_start,
                persistence_start: end + delay_end,
                state_var: sv,
                value: value.into(),
            });
        }

        // Conditions
        for mut condition in conditions {
            let sign_end: String = condition.pop().unwrap();
            let sign_end: Vec<&str> = sign_end.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
            let value_end: &str = sign_end[0];
            let delay_end: i32 = sign_end[1].parse().unwrap();
            let sign_start: String = condition.pop().unwrap();
            let sign_start: Vec<&str> = sign_start.split(" - ").collect::<Vec<&str>>()[0].split(" + ").collect();
            let value_start: &str = sign_start[0];
            let delay_start: i32 = sign_start[1].parse().unwrap();
            let value: bool = condition.pop().unwrap().to_lowercase().parse().unwrap();

            let mut sv: Vec<SAtom> = vec![context
                .typed_sym(context.model.get_symbol_table().id(&condition[0]).unwrap())
                .into()];
            for arg in condition.iter().skip(1) {
                let value_arg = arg.split(" - ").collect::<Vec<&str>>()[0];
                sv.push(*args.get(value_arg).unwrap());
            }

            let has_effect_on_same_state_variable = ch
                .effects
                .iter()
                .map(|e| e.state_var.as_slice())
                .any(|x| x == sv.as_slice());

            let start = if value_start == "__start__" || value_start == "__now__" || value_start == ch_value_start {
                ch.start
            } else if value_start == "__end__" || value_start == ch_value_end {
                ch.end
            } else {
                panic!("unsupported start case: {}", value_start);
            };

            let end = if value_end == "__end__" || value_end == ch_value_end {
                ch.end
            } else if value_end == "__start__" || value_end == ch_value_start {
                ch.start
            } else if value_end == "__now__" {
                if kind == ChronicleKind::Method || has_effect_on_same_state_variable {
                    ch.start
                } else {
                    ch.end
                }
            } else {
                panic!("unsupported end case: {}", value_end);
            };

            ch.conditions.push(Condition {
                start: start + delay_start,
                end: end + delay_end,
                state_var: sv,
                value: value.into(),
            });
        }

        // Constraints
        for constraint in constraints {
            let left_value: Vec<&str> = constraint[0].split(" - ").collect();
            let left_type: &str = left_value[1];
            let left_value: &str = left_value[0];
            let right_value: Vec<&str> = constraint[2].split(" - ").collect();
            let right_type: &str = right_value[1];
            let right_value: &str = right_value[0];
            let relation: &str = &constraint[1];

            if left_type != right_type {
                panic!(
                    "cannot create a constraint between different types: {} and {}",
                    left_type, right_type
                );
            }

            let constr: Constraint;
            if left_type == "__timepoint__" {
                let left_var: Vec<&str> = left_value.split(" + ").collect();
                let left_delay: i32 = left_var[1].parse().unwrap();
                let left_value: FAtom = if left_var[0] == "__start__" {
                    ch.start
                } else if left_var[0] == "__end__" {
                    ch.end
                } else {
                    panic!("unsupported start case: {}", left_var[0]);
                };

                let right_var: Vec<&str> = right_value.split(" + ").collect();
                let right_delay: i32 = right_var[1].parse().unwrap();
                let right_value: FAtom = if right_var[0] == "__start__" {
                    ch.start
                } else if right_var[0] == "__end__" {
                    ch.end
                } else {
                    panic!("unsupported start case: {}", right_var[0]);
                };

                constr = if relation == "==" {
                    Constraint::eq(left_value + left_delay, right_value + right_delay)
                } else if relation == "!=" {
                    Constraint::neq(left_value + left_delay, right_value + right_delay)
                } else if relation == "<" {
                    Constraint::lt(left_value + left_delay, right_value + right_delay)
                } else if relation == ">" {
                    Constraint::lt(right_value + right_delay, left_value + left_delay)
                } else if relation == "<=" {
                    Constraint::lt(left_value + left_delay, right_value + right_delay + FAtom::EPSILON)
                } else if relation == ">=" {
                    Constraint::lt(right_value + right_delay, left_value + left_delay + FAtom::EPSILON)
                } else {
                    panic!("unknow relation {}", relation);
                };
            } else {
                let left_var: SAtom = *args.get(left_value).unwrap();
                let right_var: SAtom = *args.get(right_value).unwrap();

                constr = if relation == "==" {
                    Constraint::eq(left_var, right_var)
                } else if relation == "!=" {
                    Constraint::neq(left_var, right_var)
                } else {
                    panic!("unsupported relation {} for no timepoints", relation);
                };
            }

            ch.constraints.push(constr);
        }

        // Subtasks
        if let Some(subtasks) = subtasks {
            if let Some(subtasks_constraints) = subtasks_constraints {
                add_task_network(c, &mut ch, context, Some(args), subtasks, subtasks_constraints);
            }
        }

        // Creation
        self.templates.push(ChronicleTemplate {
            label: Some(sign[0].clone()),
            parameters: params,
            chronicle: ch,
        });
    }
}

/// Add a new task network with constraints to the given chronicle.
///
/// Parameters
/// ----------
/// - c : Container
///     - Container used for the subtasks creations.
/// - ch : Chronicle
///     - Chronicle where the task network will be added.
/// - context : Ctx
///     - The contet of the problem.
/// - args: HashMap<&str, SAtom>, optional
///     - Mapping of an argument value with its associated SAtom.
/// - tasks : list of TempSign
///     - List of task temporal signatures of the task network.
/// - constraints : list of temporal constraints
///     - List of temporal constraints between the tasks of the task network.
fn add_task_network(
    c: Container,
    ch: &mut Chronicle,
    context: &mut Ctx,
    args: Option<HashMap<&str, SAtom>>,
    tasks: Vec<TempSign>,
    constraints: Vec<TemporalConstraint>,
) {
    let mut task_starts: HashMap<String, FAtom> = HashMap::new();
    let mut task_ends: HashMap<String, FAtom> = HashMap::new();

    for mut task in tasks {
        let end = task.pop().unwrap();
        let start = task.pop().unwrap();
        let tn = if let Some(args) = args.clone() {
            let mut tn = vec![context
                .typed_sym(context.model.get_symbol_table().id(&task[0]).unwrap())
                .into()];
            for arg in task.iter().skip(1) {
                let value_arg = arg.split(" - ").collect::<Vec<&str>>()[0];
                tn.push(*args.get(value_arg).unwrap());
            }
            tn
        } else {
            satom_from_signature(context, task)
        };
        let prez = ch.presence;
        let st = create_subtask(context, c, prez, None, tn);
        task_ends.insert(end, st.end);
        task_starts.insert(start, st.start);
        ch.subtasks.push(st);
    }

    for constraint in constraints {
        let first_delay: i32 = constraint[0].split(" - ").collect::<Vec<&str>>()[0]
            .split(" + ")
            .collect::<Vec<&str>>()[1]
            .parse()
            .unwrap();
        let second_delay: i32 = constraint[2].split(" - ").collect::<Vec<&str>>()[0]
            .split(" + ")
            .collect::<Vec<&str>>()[1]
            .parse()
            .unwrap();
        let relation = &constraint[1];

        let first_atom: FAtom = *task_starts
            .get(&constraint[0])
            .unwrap_or_else(|| task_ends.get(&constraint[0]).unwrap());
        let second_atom: FAtom = *task_starts
            .get(&constraint[2])
            .unwrap_or_else(|| task_ends.get(&constraint[2]).unwrap());

        let new_constraint = if relation == "==" {
            Constraint::eq(first_atom + first_delay, second_atom + second_delay)
        } else if relation == "!=" {
            Constraint::neq(first_atom + first_delay, second_atom + second_delay)
        } else if relation == "<" {
            Constraint::lt(first_atom + first_delay, second_atom + second_delay)
        } else if relation == ">" {
            Constraint::lt(first_atom + second_delay, second_atom + first_delay)
        } else if relation == "<=" {
            Constraint::lt(first_atom + first_delay, second_atom + second_delay + FAtom::EPSILON)
        } else if relation == ">=" {
            Constraint::lt(first_atom + second_delay, second_atom + first_delay + FAtom::EPSILON)
        } else {
            panic!("unknow relation {}", relation);
        };

        ch.constraints.push(new_constraint);
    }
}

/// Creates a subtask for the problem.
///
/// Parameters
/// ----------
/// - context : Ctx
///     - The contet of the problem.
/// - c : Container
///     - Container used for the subtasks creations.
/// - pres : Lit
///     - Whether or not the subtask is part of the solution.
/// - params : list of Variable, optional
///     - Variables with which the solver will be able to interact.
/// - task_name : list of SAtom
///     - The task to create with its name and its arguments.
///       Typically the return of `satom_from_signature()`.
fn create_subtask(
    context: &mut Ctx,
    c: Container,
    prez: Lit,
    mut params: Option<&mut Vec<Variable>>,
    task_name: Vec<SAtom>,
) -> SubTask {
    let start = context
        .model
        .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::TaskStart);
    let end = context
        .model
        .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::TaskEnd);
    if let Some(ref mut p) = params {
        p.push(start.into());
        p.push(end.into());
    }
    let start = FAtom::from(start);
    let end = FAtom::from(end);
    let id = None;
    SubTask {
        id,
        start,
        end,
        task_name,
    }
}

/// Find the `SAtom` in the context, corresponding to the given signature.
fn satom_from_signature(context: &mut Ctx, signature: Sign) -> Vec<SAtom> {
    let mut sv: Vec<SAtom> = vec![];
    for arg in signature {
        let arg_value = arg.split(" - ").collect::<Vec<&str>>()[0];
        sv.push(
            context
                .typed_sym(context.model.get_symbol_table().id(arg_value).unwrap())
                .into(),
        );
    }
    sv
}

/// A python module to generate a planning problem with chronicles.
#[pymodule]
fn chronicles(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<ChronicleProblem>()?;

    Ok(())
}

//region Solver
/// This part is mainly a copy of `aries/planners/src/bin/lcp.rs`
fn run_problem(problem: &mut Problem, output_file: &str) {
    println!("===== Preprocessing ======");
    aries_planning::chronicles::preprocessing::preprocess(problem);
    println!("==========================");

    let max_depth = u32::MAX;
    let min_depth = if hierarchical_is_non_recursive(problem) {
        max_depth // non recursive htn: bounded size, go directly to max
    } else {
        0
    };

    for n in min_depth..=max_depth {
        let depth_string = if n == u32::MAX {
            "∞".to_string()
        } else {
            n.to_string()
        };
        println!("{} Solving with {} actions", depth_string, depth_string);
        let start = Instant::now();
        let mut pb = FiniteProblem {
            model: problem.context.model.clone(),
            origin: problem.context.origin(),
            horizon: problem.context.horizon(),
            chronicles: problem.chronicles.clone(),
            tables: problem.context.tables.clone(),
        };
        populate_with_task_network(&mut pb, problem, n).unwrap();
        println!("  [{:.3}s] Populated", start.elapsed().as_secs_f32());
        let start = Instant::now();
        let result = solve(&pb);
        println!("  [{:.3}s] solved", start.elapsed().as_secs_f32());
        if let Some(x) = result {
            // println!("{}", format_partial_plan(&pb, &x)?);
            println!("  Solution found");
            let plan = format!(
                "\n**** Decomposition ****\n\n\
                    {}\n\n\
                    **** Plan ****\n\n\
                    {}",
                format_hddl_plan(&pb, &x).unwrap(),
                format_pddl_plan(&pb, &x).unwrap()
            );
            println!("{}", plan);
            let mut file = File::create(output_file).unwrap();
            file.write_all(plan.as_bytes()).unwrap();
            break;
        }
    }
}

fn init_solver(pb: &FiniteProblem) -> Box<Solver> {
    let model = encode(pb).unwrap();
    let stn_config = StnConfig {
        theory_propagation: TheoryPropagationLevel::Full,
        ..Default::default()
    };

    let mut solver = Box::new(aries_solver::solver::Solver::new(model));
    solver.add_theory(|tok| StnTheory::new(tok, stn_config));
    solver
}

/// Default set of strategies for HTN problems
const HTN_DEFAULT_STRATEGIES: [Strat; 2] = [Strat::Activity, Strat::Forward];

#[derive(Copy, Clone, Debug)]
enum Strat {
    /// Activity based search
    Activity,
    /// Mimics forward search in HTN problems.
    Forward,
}

impl Strat {
    /// Configure the given solver to follow the strategy.
    pub fn adapt_solver(self, solver: &mut Solver, problem: &FiniteProblem) {
        match self {
            Activity => {
                // nothing, activity based search is the default configuration
            }
            Forward => solver.set_brancher(ForwardSearcher::new(Arc::new(problem.clone()))),
        }
    }
}

impl FromStr for Strat {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "1" | "act" | "activity" => Ok(Activity),
            "2" | "fwd" | "forward" => Ok(Forward),
            _ => Err(format!("Unknown search strategy: {}", s)),
        }
    }
}

fn solve(pb: &FiniteProblem) -> Option<std::sync::Arc<SavedAssignment>> {
    let solver = init_solver(pb);
    let strats: &[Strat] = &HTN_DEFAULT_STRATEGIES;
    let mut solver =
        aries_solver::parallel_solver::ParSolver::new(solver, strats.len(), |id, s| strats[id].adapt_solver(s, pb));

    let found_plan = solver.solve().unwrap();

    if let Some(solution) = found_plan {
        solver.print_stats();
        Some(solution)
    } else {
        None
    }
}
//endregion
