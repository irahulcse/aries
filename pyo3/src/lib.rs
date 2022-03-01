use crate::Strat::{Activity, Forward};
use aries_core::{Lit, INT_CST_MAX};
use aries_model::extensions::{SavedAssignment, Shaped};
use aries_model::lang::{FAtom, SAtom, Type, Variable};
use aries_model::symbols::SymbolTable;
use aries_model::types::TypeHierarchy;
use aries_planners::encode::{encode, populate_with_task_network, populate_with_template_instances};
use aries_planners::fmt::{format_hddl_plan, format_pddl_plan};
use aries_planners::forward_search::ForwardSearcher;
use aries_planners::Solver;
use aries_planning::chronicles::analysis::hierarchical_is_non_recursive;
use aries_planning::chronicles::constraints::Constraint;
use aries_planning::chronicles::{
    Chronicle, ChronicleInstance, ChronicleKind, ChronicleOrigin, ChronicleTemplate, Condition, Container, Ctx, Effect,
    FiniteProblem, Problem, StateFun, SubTask, VarType, TIME_SCALE,
};
use aries_solver::parallel_solver::ParSolver;
use aries_tnet::theory::{StnConfig, StnTheory, TheoryPropagationLevel};
use aries_utils::input::Sym;
use pyo3::prelude::*;
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

/// A python class to generate a planning problem with chronicles.
#[pyclass]
struct ChronicleProblem {
    types: Vec<(Sym, Option<Sym>)>,
    symbols: Vec<(Sym, Sym)>,
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
    /// Sets all attributes to their default values.
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
            symbols: vec![],
            symbol_table: None,
            state_variables: vec![],
            context: None,
            init_ch: None,
            templates: vec![],
        }
    }

    /// Allows the user to add their own hierarchical types.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the type.
    /// - parent : str, optional
    ///     - The symbol of the parent of the type.
    fn add_type(&mut self, sym: &str, parent: Option<&str>) {
        if let Some(parent) = parent {
            self.types.push((sym.into(), Some(parent.into())));
        } else {
            self.types.push((sym.into(), Some(OBJECT_TYPE.into())));
        }
    }

    /// Allows the user to add the symbol of an object.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the object.
    /// - _type : str
    ///     - The type of the object.
    fn add_object_symbol(&mut self, sym: &str, _type: &str) {
        self.symbols.push((sym.into(), _type.into()))
    }

    /// Allows the user to add the symbol of a constant.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the constant.
    /// - _type : str
    ///     - The type of the constant.
    fn add_constant_symbol(&mut self, sym: &str, _type: &str) {
        self.symbols.push((sym.into(), _type.into()))
    }

    /// Allows the user to add the symbol of a predicate.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the predicate.
    fn add_predicate_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), PREDICATE_TYPE.into()))
    }

    /// Allows the user to add the symbol of an action.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the action.
    fn add_action_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), ACTION_TYPE.into()))
    }

    /// Allows the user to add the symbol of a durative action.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the durative action.
    fn add_durative_action_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), DURATIVE_ACTION_TYPE.into()))
    }

    /// Allows the user to add the symbol of a task.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the task.
    fn add_task_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), ABSTRACT_TASK_TYPE.into()))
    }

    /// Allows the user to add the symbol of a method.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the method.
    fn add_method_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), METHOD_TYPE.into()))
    }

    /// Allows the user to add the symbol of a function.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the function.
    fn add_function_symbol(&mut self, sym: &str) {
        self.symbols.push((sym.into(), FUNCTION_TYPE.into()))
    }

    /// Creates the symbol table used for the creation of the state variables and the context.
    /// Must be called when all symbols have been created.
    fn create_symbol_table(&mut self) {
        self.symbol_table =
            Some(SymbolTable::new(TypeHierarchy::new(self.types.to_vec()).unwrap(), self.symbols.to_vec()).unwrap());
    }

    /// Allows the user to add a predicate.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the predicate.
    /// - args : list of str
    ///     - The types of the predicate arguments.
    fn add_predicate(&mut self, sym: &str, args: Vec<&str>) {
        self.add_state_variable(sym, args, Type::Bool);
    }

    /// Allows the user to add a function.
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the function.
    /// - args : list of str
    ///     - The types of the function arguments.
    fn add_function(&mut self, sym: &str, args: Vec<&str>) {
        self.add_state_variable(sym, args, Type::Int);
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

    /// Allows the user to add a goal.
    ///
    /// Parameters
    /// ----------
    /// - state_var: list of str
    ///     - State variable name followed by the type of its arguments.
    /// - value : bool
    ///     - Value of the state variable to be achieved.
    fn add_goal(&mut self, state_var: Vec<&str>, value: bool) {
        let sv = self.satom_from_signature(state_var);
        let init_ch = self.init_ch.as_mut().unwrap();
        init_ch.conditions.push(Condition {
            start: init_ch.end,
            end: init_ch.end,
            state_var: sv,
            value: value.into(),
        });
    }

    /// Allows the user to add a goal as a task.
    ///
    /// Parameters
    /// ----------
    /// - task : list of str
    ///     - Task name and followed by the type of its arguments.
    fn add_goal_task(&mut self, state_var: Vec<&str>) {
        let init_container = Container::Instance(0);
        let tn = self.satom_from_signature(state_var);
        let prez = self.init_ch.as_ref().unwrap().presence;
        let context = self.context.as_mut().unwrap();
        let st = create_subtask(context, init_container, prez, None, tn);
        self.init_ch.as_mut().unwrap().subtasks.push(st);
    }

    /// Allows the user to add an initial state.
    ///
    /// Parameters
    /// ----------
    /// - state_var : list of str
    ///     - State variable name followed by the type of its arguments.
    /// - value : bool
    ///     - Value of the state variable to be initialised.
    fn add_init(&mut self, state_var: Vec<&str>, value: bool) {
        let sv = self.satom_from_signature(state_var);
        let init_ch = self.init_ch.as_mut().unwrap();
        init_ch.effects.push(Effect {
            transition_start: init_ch.start,
            persistence_start: init_ch.start,
            state_var: sv,
            value: value.into(),
        });
    }

    /// Allows the user to add an action.
    ///
    /// Parameters
    /// ----------
    /// - action : list of str
    ///     - Action name followed by the type of its arguments.
    /// - conditions : list of list of str
    ///     - List of preconditions for this action. A precondition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `action`.
    /// - effects : list of list of str
    ///     - List of effects done by this action. An effect has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `action`.
    fn add_action(&mut self, action: Vec<&str>, conditions: Vec<Vec<&str>>, effects: Vec<Vec<&str>>) {
        self.add_template(
            action,                // Sign
            ChronicleKind::Action, // Template type
            None,                  // Duration
            Some(conditions),      // Conditions
            None,                  // Timed conditions
            Some(effects),         // Effects
            None,                  // Timed effects
            None,                  // Task
            None,                  // Ordered subtasks
            None,                  // Unordered subtaks
            None,                  // Grounded task
            None,                  // Grounded ordered subtasks
            None,                  // Grounded unordered subtaks
        );
    }

    /// Allows the user to add a durative action.
    ///
    /// Parameters
    /// ----------
    /// - action : list of str
    ///     - Action name followed by the type of its arguments.
    /// - duration : i32
    ///     - Duration of the durative action.
    /// - conditions : list of list of str
    ///     - List of conditions for a durative action. A condition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value, when]`
    ///     where `pos_argi` is the position of the argument in `action` and `when` is in `["start", "end", "over all"]`.
    /// - effects : list of list of str
    ///     - List of effects for a durative action. An effect has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value, when]`
    ///     where `pos_argi` is the position of the argument in `action` and `when` is in `["start", "end", "over all"]`.
    fn add_durative_action(
        &mut self,
        action: Vec<&str>,
        duration: i32,
        conditions: Vec<Vec<&str>>,
        effects: Vec<Vec<&str>>,
    ) {
        self.add_template(
            action,                        // Sign
            ChronicleKind::DurativeAction, // Template type
            Some(duration),                // Duration
            None,                          // Conditions
            Some(conditions),              // Timed conditions
            None,                          // Effects
            Some(effects),                 // Timed effects
            None,                          // Task
            None,                          // Ordered subtasks
            None,                          // Unordered subtaks
            None,                          // Grounded task
            None,                          // Grounded ordered subtasks
            None,                          // Grounded unordered subtaks
        );
    }

    /// Allows the user to add a method.
    ///
    /// Parameters
    /// ----------
    /// - method : list of str
    ///     - Method name followed by the type of its arguments.
    /// - task : list of str
    ///     - Task name followed by the position of the arguments in `method`.
    /// - conditions : list of list of str
    ///     - List of conditions for a durative action. A condition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `method`.
    /// - ordered_subtasks : list of list of str
    ///     - List of the ordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    /// - unordered_subtasks : list of list of str
    ///     - List of the unordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    fn add_method(
        &mut self,
        method: Vec<&str>,
        task: Vec<&str>,
        conditions: Vec<Vec<&str>>,
        ordered_subtasks: Vec<Vec<&str>>,
        unordered_subtasks: Vec<Vec<&str>>,
    ) {
        self.add_template(
            method,                   // Sign
            ChronicleKind::Method,    // Template type
            None,                     // Duration
            Some(conditions),         // Conditions
            None,                     // Timed conditions
            None,                     // Effects
            None,                     // Timed effects
            Some(task),               // Task
            Some(ordered_subtasks),   // Ordered subtasks
            Some(unordered_subtasks), // Unordered subtaks
            None,                     // Grounded task
            None,                     // Grounded ordered subtasks
            None,                     // Grounded unordered subtaks
        );
    }

    /// Allows the user to add a grounded method.
    ///
    /// Parameters
    /// ----------
    /// - method : list of str
    ///     - Method name followed by the type of its arguments.
    /// - task : list of str
    ///     - Task name followed by the position of the arguments in `method`.
    /// - conditions : list of list of str
    ///     - List of conditions for a durative action. A condition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `method`.
    /// - ordered_subtasks : list of list of str
    ///     - List of the ordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    /// - unordered_subtasks : list of list of str
    ///     - List of the unordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    fn add_grounded_method(
        &mut self,
        method: Vec<&str>,
        task: Vec<&str>,
        conditions: Vec<Vec<&str>>,
        ordered_subtasks: Vec<Vec<&str>>,
        unordered_subtaks: Vec<Vec<&str>>,
    ) {
        self.add_template(
            method,                  // Sign
            ChronicleKind::Method,   // Template type
            None,                    // Duration
            Some(conditions),        // Conditions
            None,                    // Timed conditions
            None,                    // Effects
            None,                    // Timed effects
            None,                    // Task
            None,                    // Ordered subtasks
            None,                    // Unordered subtaks
            Some(task),              // Grounded task
            Some(ordered_subtasks),  // Grounded ordered subtasks
            Some(unordered_subtaks), // Grounded unordered subtaks
        )
    }

    /// Final method to call. Solve the problem defined by this instance.
    ///
    /// Parameters
    /// ----------
    /// - htn : bool
    ///     - Whether or not the problem is hierarchical.
    fn solve(&self, htn: bool) {
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
            htn,
        );
    }
}

/// Private methods of ChronicleProblem.
impl ChronicleProblem {
    /// Generic method to create a state variable (i.e. predicate or function).
    ///
    /// Parameters
    /// ----------
    /// - sym : str
    ///     - The symbol of the state variable.
    /// - args : list of str
    ///     - The types of the state variable arguments.
    /// - return_type : Type
    ///     - The type of the state variable:
    ///         - Type::Bool for a predicate
    ///         - Type::Int for a function
    fn add_state_variable(&mut self, sym: &str, args: Vec<&str>, return_type: Type) {
        let symbol_table = self.symbol_table.as_ref().unwrap();
        let symbol = symbol_table.id(sym).unwrap();
        let mut tpe = vec![];
        for arg in args {
            tpe.push(Type::Sym(symbol_table.types.id_of(arg).unwrap()));
        }
        tpe.push(return_type);
        self.state_variables.push(StateFun { sym: symbol, tpe });
    }

    /// Parameters
    /// ----------
    /// - sign : list of str
    ///     - The signature to find.
    ///       It is composed of the name followed by the arguments.
    ///
    /// Returns
    /// -------
    /// - list of `SAtom`
    ///     - The `SAtom`s corresponding to the signature.
    fn satom_from_signature(&mut self, sign: Vec<&str>) -> Vec<SAtom> {
        let context = self.context.as_ref().unwrap();
        let mut sv: Vec<SAtom> = vec![];
        for var in sign {
            sv.push(
                context
                    .typed_sym(context.model.get_symbol_table().id(var).unwrap())
                    .into(),
            );
        }
        sv
    }

    /// Generic method to add a template (i.e. action, durative_action, method).
    ///
    /// Parameters
    /// ----------
    /// - sign : list of str
    ///     - Template name followed by the type of its arguments.
    /// - template_type : ChronicleKind
    ///     - Defines if the template is an action, a durative action or a method.
    /// - duration : i32, optional
    ///     - The duration for a durative action.
    /// - conditions : list of list of str, optional
    ///     - List of preconditions. A precondition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `sign`.
    /// - timed_conditions : list of list of str, optional
    ///     - List of conditions for a durative action. A condition has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value, when]`
    ///     where `pos_argi` is the position of the argument in `sign` and `when` is in `["start", "end", "over all"]`.
    /// - effects : list of list of str, optional
    ///     - List of effects. An effect has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value]`
    ///     where `pos_argi` is the position of the argument in `sign`.
    /// - timed_effects : list of list of str, optional
    ///     - List of effects for a durative action. An effect has the following format:
    ///     `[name, pos_arg1, pos_arg2, ..., value, when]`
    ///     where `pos_argi` is the position of the argument in `sign` and `when` is in `["start", "end", "over all"]`.
    /// - task : list of str, optional
    ///     - Task name followed by the position of the arguments in `method`.
    /// - ordered_subtasks : list of list of str, optional
    ///     - List of the ordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    /// - unordered_subtasks : list of list of str
    ///     - List of the unordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by the position of the arguments in `method`.
    /// - grounded_task : list of str, optional
    ///     - Grounded task name followed by the constants parameters.
    /// - grounded_ordered_subtasks : list of list of str, optional
    ///     - List of the grounded ordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by its constant parameters.
    /// - grounded_unordered_subtasks : list of list of str
    ///     - List of the grounded unordered subtasks done by this method.
    ///     A subtasks is the subtask name followed by its constant parameters.
    fn add_template(
        &mut self,
        sign: Vec<&str>,
        template_type: ChronicleKind,
        duration: Option<i32>,
        conditions: Option<Vec<Vec<&str>>>,
        timed_conditions: Option<Vec<Vec<&str>>>,
        effects: Option<Vec<Vec<&str>>>,
        timed_effects: Option<Vec<Vec<&str>>>,
        task: Option<Vec<&str>>,
        ordered_subtasks: Option<Vec<Vec<&str>>>,
        unordered_subtasks: Option<Vec<Vec<&str>>>,
        grounded_task: Option<Vec<&str>>,
        grounded_ordered_subtasks: Option<Vec<Vec<&str>>>,
        grounded_unordered_subtasks: Option<Vec<Vec<&str>>>,
    ) {
        let context = self.context.as_mut().unwrap();

        let c = Container::Template(self.templates.len());
        let mut params: Vec<Variable> = vec![];

        // Presence
        let prez_var = context.model.new_bvar(c / VarType::Presence);
        params.push(prez_var.into());
        let prez = prez_var.true_lit();

        // Start & End
        let start = context
            .model
            .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::ChronicleStart);
        params.push(start.into());
        let start = FAtom::from(start);
        let end: FAtom = match template_type {
            ChronicleKind::Problem => panic!("unsupported case"),
            ChronicleKind::Method | ChronicleKind::DurativeAction => {
                let end = context
                    .model
                    .new_optional_fvar(0, INT_CST_MAX, TIME_SCALE, prez, c / VarType::ChronicleEnd);
                params.push(end.into());
                end.into()
            }
            ChronicleKind::Action => start + FAtom::EPSILON,
        };

        // Name & arguments
        let mut name: Vec<SAtom> = vec![context
            .typed_sym(context.model.get_symbol_table().id(sign[0]).unwrap())
            .into()];
        for s in sign.iter().skip(1) {
            let arg = context.model.new_optional_sym_var(
                context.model.get_symbol_table().types.id_of(*s).unwrap(),
                prez,
                c / VarType::Parameter,
            );
            params.push(arg.into());
            name.push(arg.into());
        }

        // Task
        let task = if let Some(task) = task {
            let mut tn = vec![context
                .typed_sym(context.model.get_symbol_table().id(task[0]).unwrap())
                .into()];
            for i in 1..task.len() {
                tn.push(name[task[i].parse::<usize>().unwrap()]);
            }
            tn
        } else if let Some(task) = grounded_task {
            let mut tn = vec![];
            for arg in task {
                tn.push(
                    context
                        .typed_sym(context.model.get_symbol_table().id(arg).unwrap())
                        .into(),
                );
            }
            tn
        } else {
            name.clone()
        };

        // Chronicle
        let mut ch = Chronicle {
            kind: template_type,
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

        // Effects
        if let Some(effects) = effects {
            for effect in effects {
                let mut sv: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(effect[0]).unwrap())
                    .into()];
                for i in 1..effect.len() - 1 {
                    sv.push(name[effect[i].parse::<usize>().unwrap()]);
                }
                ch.effects.push(Effect {
                    transition_start: ch.start,
                    persistence_start: ch.end,
                    state_var: sv,
                    value: effect[effect.len() - 1].parse::<bool>().unwrap().into(),
                });
            }
        };

        // Timed effects
        if let Some(effects) = timed_effects {
            for effect in effects {
                let mut sv: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(effect[0]).unwrap())
                    .into()];
                for i in 1..effect.len() - 2 {
                    sv.push(name[effect[i].parse::<usize>().unwrap()]);
                }
                let time = match effect[effect.len() - 1] {
                    "start" => ch.start,
                    "end" => ch.end,
                    _ => ch.start,
                };
                ch.effects.push(Effect {
                    transition_start: time,
                    persistence_start: time + FAtom::EPSILON,
                    state_var: sv,
                    value: effect[effect.len() - 2].parse::<bool>().unwrap().into(),
                });
            }
        };

        // Conditions
        if let Some(conditions) = conditions {
            for condition in conditions {
                let mut sv: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(condition[0]).unwrap())
                    .into()];
                for i in 1..condition.len() - 1 {
                    sv.push(name[condition[i].parse::<usize>().unwrap()]);
                }
                let has_effect_on_same_state_variable = ch
                    .effects
                    .iter()
                    .map(|e| e.state_var.as_slice())
                    .any(|x| x == sv.as_slice());
                let end = if has_effect_on_same_state_variable || template_type == ChronicleKind::Method {
                    ch.start
                } else {
                    ch.end
                };
                ch.conditions.push(Condition {
                    start: ch.start,
                    end,
                    state_var: sv,
                    value: condition[condition.len() - 1].parse::<bool>().unwrap().into(),
                });
            }
        }

        // Timed conditions
        if let Some(conditions) = timed_conditions {
            for condition in conditions {
                let mut sv: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(condition[0]).unwrap())
                    .into()];
                for i in 1..condition.len() - 2 {
                    sv.push(name[condition[i].parse::<usize>().unwrap()]);
                }
                let time = condition[condition.len() - 1];
                let start = match time {
                    "start" => ch.start,
                    "end" => ch.end,
                    "over all" => ch.start,
                    _ => ch.start,
                };
                let end = match time {
                    "start" => ch.start,
                    "end" => ch.end,
                    "over all" => ch.end,
                    _ => ch.end,
                };
                ch.conditions.push(Condition {
                    start,
                    end,
                    state_var: sv,
                    value: condition[condition.len() - 2].parse::<bool>().unwrap().into(),
                });
            }
        }

        // Duration
        if let Some(duration) = duration {
            ch.constraints.push(Constraint::duration(duration));
        }

        // Ordered subtasks
        if let Some(subtasks) = ordered_subtasks {
            let mut previous_end = None;
            for subtask in subtasks {
                let mut tn: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(subtask[0]).unwrap())
                    .into()];
                for i in 1..subtask.len() {
                    tn.push(name[subtask[i].parse::<usize>().unwrap()]);
                }
                let st = create_subtask(context, c, ch.presence, Some(&mut params), tn);
                if let Some(previous_end) = previous_end {
                    ch.constraints.push(Constraint::lt(previous_end, st.start))
                }
                previous_end = Some(st.end);
                ch.subtasks.push(st);
            }
        };
        if let Some(subtasks) = grounded_ordered_subtasks {
            let mut previous_end = None;
            for subtask in subtasks {
                let mut tn = vec![];
                for arg in subtask {
                    tn.push(
                        context
                            .typed_sym(context.model.get_symbol_table().id(arg).unwrap())
                            .into(),
                    );
                }
                let st = create_subtask(context, c, ch.presence, Some(&mut params), tn);
                if let Some(previous_end) = previous_end {
                    ch.constraints.push(Constraint::lt(previous_end, st.start))
                }
                previous_end = Some(st.end);
                ch.subtasks.push(st);
            }
        };

        // Unordered subtasks
        if let Some(subtasks) = unordered_subtasks {
            for subtask in subtasks {
                let mut tn: Vec<SAtom> = vec![context
                    .typed_sym(context.model.get_symbol_table().id(subtask[0]).unwrap())
                    .into()];
                for i in 1..subtask.len() {
                    tn.push(name[subtask[i].parse::<usize>().unwrap()]);
                }
                let st = create_subtask(context, c, ch.presence, Some(&mut params), tn);
                ch.subtasks.push(st);
            }
        };
        if let Some(subtasks) = grounded_unordered_subtasks {
            for subtask in subtasks {
                let mut tn = vec![];
                for arg in subtask {
                    tn.push(
                        context
                            .typed_sym(context.model.get_symbol_table().id(arg).unwrap())
                            .into(),
                    );
                }
                let st = create_subtask(context, c, ch.presence, Some(&mut params), tn);
                ch.subtasks.push(st);
            }
        };

        // Creation
        self.templates.push(ChronicleTemplate {
            label: Some(sign[0].into()),
            parameters: params,
            chronicle: ch,
        });
    }
}

/// Creates a subtask for the problem.
///
/// Parameters
/// ----------
/// - goal : bool
///     - Whether or not the task is for the goal.
/// - c : Container
/// - params : list of variable, optional
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

/// A python module to generate a planning problem with chronicles.
#[pymodule]
fn chronicles(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<ChronicleProblem>()?;

    Ok(())
}

//region Solver
/// This part is mainly a copy of `aries/planners/src/bin/lcp.rs`
fn run_problem(problem: &mut Problem, htn_mode: bool) {
    println!("===== Preprocessing ======");
    aries_planning::chronicles::preprocessing::preprocess(problem);
    println!("==========================");

    let max_depth = u32::MAX;
    let min_depth = if htn_mode && hierarchical_is_non_recursive(problem) {
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
        if htn_mode {
            populate_with_task_network(&mut pb, problem, n).unwrap();
        } else {
            populate_with_template_instances(&mut pb, problem, |_| Some(n)).unwrap();
        }
        println!("  [{:.3}s] Populated", start.elapsed().as_secs_f32());
        let start = Instant::now();
        let result = solve(&pb, htn_mode);
        println!("  [{:.3}s] solved", start.elapsed().as_secs_f32());
        if let Some(x) = result {
            // println!("{}", format_partial_plan(&pb, &x)?);
            println!("  Solution found");
            let plan = if htn_mode {
                format!(
                    "\n**** Decomposition ****\n\n\
                    {}\n\n\
                    **** Plan ****\n\n\
                    {}",
                    format_hddl_plan(&pb, &x).unwrap(),
                    format_pddl_plan(&pb, &x).unwrap()
                )
            } else {
                format_pddl_plan(&pb, &x).unwrap()
            };
            println!("{}", plan);
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
/// Default set of strategies for generative (flat) problems.
const GEN_DEFAULT_STRATEGIES: [Strat; 1] = [Strat::Activity];

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

fn solve(pb: &FiniteProblem, htn_mode: bool) -> Option<std::sync::Arc<SavedAssignment>> {
    let solver = init_solver(pb);
    let strats: &[Strat] = if htn_mode {
        &HTN_DEFAULT_STRATEGIES
    } else {
        &GEN_DEFAULT_STRATEGIES
    };
    let mut solver = if htn_mode {
        aries_solver::parallel_solver::ParSolver::new(solver, strats.len(), |id, s| strats[id].adapt_solver(s, pb))
    } else {
        ParSolver::new(solver, 1, |_, _| {})
    };

    let found_plan = solver.solve().unwrap();

    if let Some(solution) = found_plan {
        solver.print_stats();
        Some(solution)
    } else {
        None
    }
}
//endregion
