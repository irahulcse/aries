use aries_core::state::Domains;
use aries_core::{Lit, INT_CST_MAX};
use aries_cp::Cp;
use aries_model::extensions::SavedAssignment;
use aries_model::extensions::Shaped;
use aries_model::lang::{FAtom, IAtom, SAtom, Type, Variable};
use aries_model::symbols::SymbolTable;
use aries_model::types::TypeHierarchy;
use aries_planners::encode::{encode, populate_with_task_network, CausalLinks};
use aries_planners::fmt::{format_causal_links, format_hddl_plan, format_pddl_plan};
use aries_planners::solver::Metric;
use aries_planners::solver::Strat;
use aries_planners::Solver;
use aries_planning::chronicles::analysis::hierarchical_is_non_recursive;
use aries_planning::chronicles::constraints::Constraint;
use aries_planning::chronicles::FiniteProblem;
use aries_planning::chronicles::{
    Chronicle, ChronicleInstance, ChronicleKind, ChronicleOrigin, ChronicleTemplate, Condition, Container, Ctx, Effect,
    Problem, StateFun, SubTask, VarType, TIME_SCALE,
};
use aries_stn::theory::StnTheory;
use aries_stn::theory::{StnConfig, TheoryPropagationLevel};
use aries_utils::input::Sym;
use pyo3::prelude::*;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
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
            cost: None,
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
            &mut vec![],
            tasks,
            constraints,
            "__GLOBAL_START__",
            "__GLOBAL_END__",
        );
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

        let start: FAtom = {
            let id_start = if value_start.len() >= 5 {
                &value_start[..5]
            } else {
                value_start
            };

            if id_start == "__s__" || id_start == "__d__" {
                ch.start
            } else if id_start == "__e__" {
                ch.end
            } else {
                panic!("unsupported start case {}", value_start)
            }
        };

        let end: FAtom = {
            let id_end = if value_end.len() >= 5 {
                &value_end[..5]
            } else {
                value_end
            };

            if id_end == "__e__" {
                ch.end
            } else if id_end == "__s__" || id_end == "__d__" {
                ch.start
            } else {
                panic!("unsupported end case {}", value_end)
            }
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
    /// - cost : integer
    ///     - Cost of the action, the solver minimize the total cost.
    fn add_action(
        &mut self,
        action: TempSign,
        constraints: Vec<Constr>,
        conditions: Vec<Cond>,
        effects: Vec<Eff>,
        cost: i32,
    ) {
        self.add_template(action, constraints, conditions, effects, None, None, None, Some(cost));
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
    ///     - List of the required tasks in order to achieve the `task`.
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
            None,
        )
    }

    /// Print data of the current problem for debug purpose.
    fn debug_fmt(&self) {
        for template in self.templates.to_vec() {
            println!("==> {:?}", template.label.unwrap());
            println!("{:#?}", template.chronicle);
        }
        println!("==> Chronicle Problem");
        println!("{:#?}", self.init_ch.as_ref().unwrap().clone());
    }

    /// Final method to call. Solve the problem defined by this instance.
    ///
    /// Parameters
    /// ----------
    /// - output_file : str
    ///     - Path to the output file where the plan will be saved.
    /// - verbose: bool
    ///     - Whether or not information must be printed in the console.
    ///
    /// Returns
    /// -------
    /// - bool
    ///     - Whether or not a solution has been found.
    fn solve(&self, output_file: &str, verbose: bool) -> bool {
        if verbose {
            self.debug_fmt();
        }
        run_problem(
            Problem {
                context: self.context.as_ref().unwrap().clone(),
                templates: self.templates.to_vec(),
                chronicles: vec![ChronicleInstance {
                    parameters: vec![],
                    origin: ChronicleOrigin::Original,
                    chronicle: self.init_ch.as_ref().unwrap().clone(),
                }],
            },
            output_file,
            verbose,
        )
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
    ///     - List of the required tasks in order to achieve the `task`.
    /// - subtasks_constraints : list of TemporalConstraint, optional
    ///     - List of temporal constraint between the subtasks.
    /// - cost : integer, optional
    ///     - Cost of the chronicle, the solver minimize the total cost.
    #[allow(clippy::too_many_arguments)] // this function has too many arguments (9/7)
    fn add_template(
        &mut self,
        mut sign: TempSign,
        constraints: Vec<Constr>,
        conditions: Vec<Cond>,
        effects: Vec<Eff>,
        task: Option<Sign>,
        subtasks: Option<Vec<TempSign>>,
        subtasks_constraints: Option<Vec<TemporalConstraint>>,
        cost: Option<i32>,
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
        let start = FAtom::from(start);
        let start = FAtom::new(start.num + ch_delay_start, start.denom);

        let end: FAtom = if kind == ChronicleKind::Action && (ch_value_start == ch_value_end) {
            start + FAtom::EPSILON
        } else {
            let end = context
                .model
                .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::ChronicleEnd);
            params.push(end.into());
            end.into()
        };
        let end = FAtom::new(end.num + ch_delay_end, end.denom);

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
            cost,
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

            let start = {
                let id_start = if value_start.len() >= 5 {
                    &value_start[..5]
                } else {
                    value_start
                };
                if id_start == "__s__" || id_start == "__d__" || value_start == ch_value_start {
                    ch.start
                } else if id_start == "__e__" || value_start == ch_value_end {
                    ch.end
                } else {
                    panic!("unsupported start case: {}", value_start);
                }
            };
            let start = FAtom::new(start.num + delay_start, start.denom);

            let end = {
                let id_end = if value_end.len() >= 5 {
                    &value_end[..5]
                } else {
                    value_end
                };

                if id_end == "__e__" || id_end == "__d__" || value_end == ch_value_end {
                    ch.end
                } else if id_end == "__s__" || value_end == ch_value_start {
                    ch.start + FAtom::EPSILON
                } else {
                    panic!("unsupported end case: {}", value_end);
                }
            };
            let end = FAtom::new(end.num + delay_end, end.denom);

            ch.effects.push(Effect {
                transition_start: start,
                persistence_start: end,
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

            let start = {
                let id_start = if value_start.len() >= 5 {
                    &value_start[..5]
                } else {
                    value_start
                };
                if id_start == "__s__" || id_start == "__d__" || value_start == ch_value_start {
                    ch.start
                } else if id_start == "__e__" || value_start == ch_value_end {
                    ch.end
                } else {
                    panic!("unsupported start case: {}", value_start);
                }
            };
            let start = FAtom::new(start.num + delay_start, start.denom);

            let end = {
                let id_end = if value_end.len() >= 5 {
                    &value_end[..5]
                } else {
                    value_end
                };

                if id_end == "__e__" || value_end == ch_value_end {
                    ch.end
                } else if id_end == "__s__" || value_end == ch_value_start {
                    ch.start
                } else if id_end == "__d__" {
                    if kind == ChronicleKind::Method || has_effect_on_same_state_variable {
                        ch.start
                    } else {
                        ch.end
                    }
                } else {
                    panic!("unsupported end case: {}", value_end);
                }
            };
            let end = FAtom::new(end.num + delay_end, end.denom);

            ch.conditions.push(Condition {
                start,
                end,
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

            let constr: Constraint = if left_type == "__timepoint__" {
                let left_var: Vec<&str> = left_value.split(" + ").collect();
                let left_delay: i32 = left_var[1].parse().unwrap();

                let left_value = {
                    let id_left = if left_var[0].len() >= 5 {
                        &left_var[0][..5]
                    } else {
                        left_var[0]
                    };

                    if id_left == "__s__" || left_var[0] == ch_value_start {
                        ch.start
                    } else if id_left == "__e__" || left_var[0] == ch_value_end {
                        ch.end
                    } else if left_var[0] == "0" {
                        FAtom::new(IAtom::ZERO, TIME_SCALE)
                    } else {
                        panic!("unsupported left case: {}", left_var[0]);
                    }
                };
                let left_value: FAtom = FAtom::new(left_value.num + left_delay, left_value.denom);

                let right_var: Vec<&str> = right_value.split(" + ").collect();
                let right_delay: i32 = right_var[1].parse().unwrap();
                let right_value = {
                    let id_right = if right_var[0].len() >= 5 {
                        &right_var[0][..5]
                    } else {
                        right_var[0]
                    };
                    if id_right == "__s__" || right_var[0] == ch_value_start {
                        ch.start
                    } else if id_right == "__e__" || right_var[0] == ch_value_end {
                        ch.end
                    } else if right_var[0] == "0" {
                        FAtom::new(IAtom::ZERO, TIME_SCALE)
                    } else {
                        panic!("unsupported right case: {}", right_var[0]);
                    }
                };
                let right_value: FAtom = FAtom::new(right_value.num + right_delay, right_value.denom);

                if relation == "==" {
                    Constraint::eq(left_value, right_value)
                } else if relation == "!=" {
                    Constraint::neq(left_value, right_value)
                } else if relation == "<" {
                    Constraint::lt(left_value, right_value)
                } else if relation == ">" {
                    Constraint::lt(right_value, left_value)
                } else if relation == "<=" {
                    Constraint::lt(left_value, right_value + FAtom::EPSILON)
                } else if relation == ">=" {
                    Constraint::lt(right_value, left_value + FAtom::EPSILON)
                } else {
                    panic!("unknown relation {}", relation);
                }
            } else {
                let left_var: SAtom = *args.get(left_value).unwrap();
                let right_var: SAtom = *args.get(right_value).unwrap();

                if relation == "==" {
                    Constraint::eq(left_var, right_var)
                } else if relation == "!=" {
                    Constraint::neq(left_var, right_var)
                } else {
                    panic!("unsupported relation {} for no timepoints", relation);
                }
            };

            ch.constraints.push(constr);
        }

        // Subtasks
        if let Some(subtasks) = subtasks {
            if let Some(subtasks_constraints) = subtasks_constraints {
                add_task_network(
                    c,
                    &mut ch,
                    context,
                    Some(args),
                    &mut params,
                    subtasks,
                    subtasks_constraints,
                    ch_value_start,
                    ch_value_end,
                );
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
///     - The context of the problem.
/// - args: HashMap<&str, SAtom>, optional
///     - Mapping of an argument value with its associated SAtom.
/// - tasks : list of TempSign
///     - List of task temporal signatures of the task network.
/// - constraints : list of temporal constraints
///     - List of temporal constraints between the tasks of the task network.
/// - ch_value_start / ch_value_end:
///     - Names of the start/end timepoints of the containing chronicle.
#[allow(clippy::too_many_arguments)] // this function has too many arguments (8/7)
fn add_task_network(
    c: Container,
    ch: &mut Chronicle,
    context: &mut Ctx,
    args: Option<HashMap<&str, SAtom>>,
    params: &mut Vec<Variable>,
    tasks: Vec<TempSign>,
    constraints: Vec<TemporalConstraint>,
    ch_value_start: &str,
    ch_value_end: &str,
) {
    let mut task_starts: HashMap<String, FAtom> = HashMap::new();
    let mut task_ends: HashMap<String, FAtom> = HashMap::new();

    for mut task in tasks {
        let end = task.pop().unwrap();
        let end_split = end.split(" - ").collect::<Vec<&str>>();
        let end_type = end_split[1];
        let end_value = end_split[0].split(" + ").collect::<Vec<&str>>()[0];
        let end = format!("{} - {}", end_value, end_type);
        let start = task.pop().unwrap();
        let start_split = start.split(" - ").collect::<Vec<&str>>();
        let start_type = start_split[1];
        let start_value = start_split[0].split(" + ").collect::<Vec<&str>>()[0];
        let start = format!("{} - {}", start_value, start_type);
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

        let start_tp = if start_value == ch_value_start {
            ch.start
        } else {
            // TODO: many naming patterns are ignored
            let start = context
                .model
                .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::TaskStart);
            params.push(start.into());
            start.into()
        };
        let end_tp = if end_value == ch_value_end {
            ch.end
        } else {
            // TODO: many naming patterns are ignored
            let end = context
                .model
                .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::TaskEnd);

            params.push(end.into());
            end.into()
        };

        task_starts.insert(start, start_tp);
        task_ends.insert(end, end_tp);

        ch.subtasks.push(SubTask {
            id: None,
            start: start_tp,
            end: end_tp,
            task_name: tn,
        });
    }

    for constraint in constraints {
        let first = &constraint[0];
        let first_split = first.split(" - ").collect::<Vec<&str>>();
        let first_type = first_split[1];
        let first_value = first_split[0].split(" + ").collect::<Vec<&str>>()[0];
        let first = format!("{} - {}", first_value, first_type);
        let first_delay: i32 = first_split[0].split(" + ").collect::<Vec<&str>>()[1].parse().unwrap();
        let second = &constraint[2];
        let second_split = second.split(" - ").collect::<Vec<&str>>();
        let second_type = second_split[1];
        let second_value = second_split[0].split(" + ").collect::<Vec<&str>>()[0];
        let second = format!("{} - {}", second_value, second_type);
        let second_delay: i32 = second_split[0].split(" + ").collect::<Vec<&str>>()[1].parse().unwrap();
        let relation = &constraint[1];

        let default_atom: FAtom = FAtom::new(IAtom::ZERO, TIME_SCALE);
        let first_atom: FAtom = *task_starts
            .get(&first)
            .unwrap_or_else(|| task_ends.get(&first).unwrap_or(&default_atom));
        let first_atom: FAtom = FAtom::new(first_atom.num + first_delay, first_atom.denom);
        let second_atom: FAtom = *task_starts
            .get(&second)
            .unwrap_or_else(|| task_ends.get(&second).unwrap_or(&default_atom));
        let second_atom: FAtom = FAtom::new(second_atom.num + second_delay, second_atom.denom);

        let new_constraint = if relation == "==" {
            Constraint::eq(first_atom, second_atom)
        } else if relation == "!=" {
            Constraint::neq(first_atom, second_atom)
        } else if relation == "<" {
            Constraint::lt(first_atom, second_atom)
        } else if relation == ">" {
            Constraint::lt(second_atom, first_atom)
        } else if relation == "<=" {
            Constraint::lt(first_atom, second_atom + FAtom::EPSILON)
        } else if relation == ">=" {
            Constraint::lt(second_atom, first_atom + FAtom::EPSILON)
        } else {
            panic!("unknown relation {}", relation);
        };

        ch.constraints.push(new_constraint);
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

macro_rules! printlnv {
    ($v: expr, $($arg:tt)*) => {
        if $v == true {
            println!($($arg)*);
        }
    };
}

//region Solver
/// This part is mainly a copy of `aries/planners/src/bin/lcp.rs`
fn run_problem(problem: Problem, output_file: &str, verbose: bool) -> bool {
    let max_depth = u32::MAX;
    let min_depth = if hierarchical_is_non_recursive(&problem) {
        max_depth
    } else {
        0
    };

    let optimize = Metric::ActionCosts;
    let resolved;

    let result = solve(problem, min_depth, max_depth, optimize, verbose);
    if let Some((finite_problem, cost, assignment, causal_links)) = result {
        resolved = true;
        let plan_out = format_plan(&finite_problem, cost, &assignment, &causal_links);
        printlnv!(verbose, "{}", plan_out);

        // Write the output to a file
        let mut file = File::create(output_file).unwrap();
        file.write_all(plan_out.as_bytes()).unwrap();
    } else {
        resolved = false;
        printlnv!(verbose, "\nNo plan found");
    }

    resolved
}

fn format_plan(problem: &FiniteProblem, cost: i32, plan: &Arc<Domains>, causal_links: &CausalLinks) -> String {
    format!(
        "\n**** Causal links ****\n\n\
            {}\n\n\
            **** Decomposition ****\n\n\
            {}\n\n\
            **** Plan ****\n\n\
            {}\n\n\
            **** Cost ****\n\n\
            {}",
        format_causal_links(problem, plan, causal_links).unwrap(),
        format_hddl_plan(problem, plan).unwrap(),
        format_pddl_plan(problem, plan).unwrap(),
        cost,
    )
}

fn solve(
    mut base_problem: Problem,
    min_depth: u32,
    max_depth: u32,
    metric: Metric,
    verbose: bool,
) -> Option<(FiniteProblem, i32, Arc<Domains>, CausalLinks)> {
    printlnv!(verbose, "===== Preprocessing ======");
    aries_planning::chronicles::preprocessing::preprocess(&mut base_problem);
    printlnv!(verbose, "==========================");

    let start = Instant::now();
    for depth in min_depth..=max_depth {
        let mut pb = FiniteProblem {
            model: base_problem.context.model.clone(),
            origin: base_problem.context.origin(),
            horizon: base_problem.context.horizon(),
            chronicles: base_problem.chronicles.clone(),
            tables: base_problem.context.tables.clone(),
        };
        let depth_string = if depth == u32::MAX {
            "∞".to_string()
        } else {
            depth.to_string()
        };
        printlnv!(verbose, "{} Solving with {} actions", depth_string, depth_string);
        populate_with_task_network(&mut pb, &base_problem, depth).unwrap();
        printlnv!(verbose, "  [{:.3}s] Populated", start.elapsed().as_secs_f32());
        let result = solve_finite_problem(&pb, metric, verbose);
        printlnv!(verbose, "  [{:.3}s] Solved", start.elapsed().as_secs_f32());

        if let Some((cost, solution, causal_links)) = result {
            // we got a valid assignment, return the corresponding plan
            return Some((pb, cost, solution, causal_links));
        }
    }
    None
}

const HTN_DEFAULT_STRATEGIES: [Strat; 2] = [Strat::Activity, Strat::Forward];

pub fn init_solver(pb: &FiniteProblem, metric: Metric) -> (Box<Solver>, Option<IAtom>, CausalLinks) {
    let (model, metric, causal_links) = encode(pb, Some(metric)).expect("Failed to encode the problem"); // TODO: report error
    let stn_config = StnConfig {
        theory_propagation: TheoryPropagationLevel::Full,
        ..Default::default()
    };

    let mut solver = Box::new(aries_solver::solver::Solver::new(model));
    solver.add_theory(|tok| StnTheory::new(tok, stn_config));
    solver.add_theory(Cp::new);
    (solver, metric, causal_links)
}

fn solve_finite_problem(
    pb: &FiniteProblem,
    metric: Metric,
    verbose: bool,
) -> Option<(i32, std::sync::Arc<SavedAssignment>, CausalLinks)> {
    let (solver, metric, causal_links) = init_solver(pb, metric);

    // select the set of strategies, based on user-input or hard-coded defaults.
    let strats: &[Strat] = &HTN_DEFAULT_STRATEGIES;
    let mut solver =
        aries_solver::parallel_solver::ParSolver::new(solver, strats.len(), |id, s| strats[id].adapt_solver(s, pb));

    let solution = solver.minimize(metric.unwrap()).unwrap();

    if let Some((cost, plan)) = solution {
        if verbose {
            solver.print_stats();
        }
        Some((cost, plan, causal_links))
    } else {
        None
    }
}
//endregion
