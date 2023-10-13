use aries::core::{Lit, INT_CST_MAX, INT_CST_MIN};
use aries::model::extensions::{AssignmentExt, Shaped};
use aries::model::lang::linear::LinearSum;
use aries::model::lang::{FAtom, IAtom, Type};
use aries::model::symbols::SymbolTable;
use aries::model::types::TypeHierarchy;
use aries::solver::parallel::SolverResult;
use aries::utils::input::Sym;
use aries_planners::encode::{encode, EncodedProblem};
use aries_planners::solver::{init_solver, Strat};
use aries_planning::chronicles::constraints::Constraint;
use aries_planning::chronicles::printer::Printer;
use aries_planning::chronicles::Container::*;
use aries_planning::chronicles::EffectOp::Assign;
use aries_planning::chronicles::VarType::*;
use aries_planning::chronicles::{
    Chronicle, ChronicleInstance, ChronicleKind, ChronicleOrigin, Condition, Container, Ctx, Effect, FiniteProblem,
    Fluent, StateVar, VarLabel, VarType, TIME_SCALE,
};
use aries_planning::parsing::pddl::TypedSymbol;
use std::sync::Arc;
use structopt::StructOpt;

#[derive(Debug, Clone, StructOpt)]
#[structopt(name = "debug_aries", rename_all = "kebab-case")]
pub struct Opt {
    #[structopt(long, short)]
    working: bool,
}

pub fn main() {
    let subscriber = tracing_subscriber::fmt()
        .with_timer(tracing_subscriber::fmt::time::Uptime::from(std::time::Instant::now()))
        // .without_time() // if activated, no time will be printed on logs (useful for counting events with `counts`)
        .with_thread_ids(true)
        .with_max_level(tracing::Level::TRACE)
        .finish();
    tracing::subscriber::set_global_default(subscriber).unwrap();
    println!("Hello, world");
    let opt = Opt::from_args();
    let fp = chronicle(opt.working);

    let EncodedProblem {
        model,
        objective: _,
        encoding,
    } = encode(&fp, None).unwrap();

    let solver = init_solver(model);
    let encoding = Arc::new(encoding);

    // select the set of strategies, based on user-input or hard-coded defaults.
    let strats: &[Strat] = &[Strat::Causal, Strat::ActivityNonTemporalFirst, Strat::Forward];

    let mut solver = aries::solver::parallel::ParSolver::new(solver, strats.len(), |id, s| {
        strats[id].adapt_solver(s, fp.clone(), encoding.clone())
    });

    let r = solver.solve(None);

    match r {
        SolverResult::Sol(ass) => {
            println!("found solution!");
            for v in ass.variables() {
                let prez = format!("[{:?}]", ass.presence_literal(v));
                let v_str = format!("{v:?}");
                print!("{prez:<6}  {v_str:<6} <- {:?}", ass.domain(v));
                if let Some(lbl) = fp.model.get_label(v) {
                    println!("    {lbl:?}");
                } else {
                    println!()
                }
            }
        }
        SolverResult::Unsat => {
            println!("unsatisfiable")
        }
        SolverResult::Timeout(_) => {}
    }
}

pub const TYPE_TIMEPOINT: &str = "*Timepoint*";
pub const TYPE_PRESENCE: &str = "*Presence*";
pub const TYPE_TASK: &str = "*Task*";
pub const TYPE_METHOD: &str = "*Method*";
pub const TYPE_ABSTRACT_TASK: &str = "*AbstractTask*";
pub const TYPE_COMMAND: &str = "*Action*";
pub const TYPE_PREDICATE: &str = "*Predicate*";
pub const TYPE_STATE_FUNCTION: &str = "*StateFunctionType*";
pub const TYPE_OBJECT_TYPE: &str = "*ObjectType*";
pub const TYPE_OBJECT: &str = "*Object*";
pub const TYPE_RESOURCE_HANDLE: &str = "*ResourceHandle*";

pub fn chronicle(working: bool) -> Arc<FiniteProblem> {
    let types: Vec<(Sym, Option<Sym>)> = vec![
        (TYPE_TASK.into(), None),
        (TYPE_ABSTRACT_TASK.into(), Some(TYPE_TASK.into())),
        (TYPE_COMMAND.into(), Some(TYPE_TASK.into())),
        (TYPE_METHOD.into(), None),
        (TYPE_PREDICATE.into(), None),
        (TYPE_STATE_FUNCTION.into(), None),
        (TYPE_OBJECT.into(), None),
        (TYPE_OBJECT_TYPE.into(), None),
    ];

    let th = TypeHierarchy::new(types).unwrap_or_else(|e| panic!("{e}"));
    let mut symbols: Vec<TypedSymbol> = vec![];

    //command symbol
    symbols.push(TypedSymbol::new("c_test", TYPE_COMMAND));

    //sf symbol
    symbols.push(TypedSymbol::new("counter", TYPE_STATE_FUNCTION));

    let symbols = symbols
        .drain(..)
        .map(|ts| (ts.symbol, ts.tpe.unwrap_or_else(|| TYPE_OBJECT.into())))
        .collect();

    let symbol_table = SymbolTable::new(th, symbols).unwrap_or_else(|e| panic!("{e}"));

    let mut state_functions = Vec::with_capacity(1);

    let counter = Fluent {
        sym: symbol_table.id("counter").unwrap(),
        signature: vec![Type::Int {
            lb: INT_CST_MIN,
            ub: INT_CST_MAX,
        }],
    };
    state_functions.push(counter);

    let mut ctx = Ctx::new(Arc::new(symbol_table), state_functions);

    let mut chronicles = vec![];
    let counter = ctx
        .get_fluent(ctx.model.get_symbol_table().id("counter").unwrap())
        .unwrap()
        .clone();

    let t_e = cst_fatom(1.0);

    let effect = Effect {
        transition_start: t_e,
        persistence_start: t_e,
        min_persistence_end: vec![],
        state_var: StateVar {
            fluent: counter.clone(),
            args: vec![],
        },
        operation: Assign(cst_iatom(2).into()),
    };

    let t1 = ctx
        .model
        .new_fvar(0, INT_CST_MAX, TIME_SCALE.get(), VarLabel(Instance(0), Reification))
        .into();

    //let t2 = t1 + FAtom::EPSILON;
    let t2 = ctx
        .model
        .new_fvar(0, INT_CST_MAX, TIME_SCALE.get(), VarLabel(Instance(0), Reification))
        .into();

    let condition = Condition {
        start: t1,
        end: t1,
        state_var: StateVar {
            fluent: counter.clone(),
            args: vec![],
        },
        value: ctx
            .model
            .new_ivar(
                INT_CST_MIN,
                INT_CST_MAX,
                VarLabel(Container::Instance(1), VarType::Reification),
            )
            .into(),
    };

    let effect_result = ctx
        .model
        .new_ivar(
            INT_CST_MIN,
            INT_CST_MAX,
            VarLabel(Container::Instance(1), VarType::Reification),
        )
        .into();

    let effect_2 = Effect {
        transition_start: t1,
        persistence_start: t2,
        min_persistence_end: vec![],
        state_var: StateVar {
            fluent: counter.clone(),
            args: vec![],
        },
        operation: Assign(effect_result),
    };

    let mut constraints = vec![];

    let mut sum_1 = LinearSum::with_lit(t1, Lit::TRUE);
    sum_1 += LinearSum::constant_rational(1, TIME_SCALE.get());
    // This use case is working
    // sum_1 += LinearSum::constant_rational(0, TIME_SCALE.get());

    sum_1 -= LinearSum::with_lit(t2, Lit::TRUE);

    let c_1 = Constraint::linear_eq_zero(sum_1);
    constraints.push(c_1);

    if working {
        //let c_3 = Constraint::eq(t2, t1 + FAtom::EPSILON);
        //constraints.push(c_3);

        let c_4 = Constraint::lt(t1, t2);
        constraints.push(c_4);
    }

    let mut sum_2 = LinearSum::with_lit::<IAtom>(condition.value.try_into().unwrap(), Lit::TRUE);
    sum_2 += LinearSum::constant_int(1);
    sum_2 -= LinearSum::with_lit::<IAtom>(effect_result.try_into().unwrap(), Lit::TRUE);

    let c_2 = Constraint::linear_eq_zero(sum_2);
    constraints.push(c_2);

    let chronicle_origin = ChronicleInstance {
        parameters: vec![],
        origin: ChronicleOrigin::Original,
        chronicle: Chronicle {
            kind: ChronicleKind::Problem,
            presence: Lit::TRUE,
            start: ctx
                .model
                .new_fvar(
                    INT_CST_MIN,
                    INT_CST_MAX,
                    TIME_SCALE.get(),
                    VarLabel(Container::Instance(0), VarType::ChronicleStart),
                )
                .into(),
            end: ctx
                .model
                .new_fvar(
                    INT_CST_MIN,
                    INT_CST_MAX,
                    TIME_SCALE.get(),
                    VarLabel(Container::Instance(0), ChronicleEnd),
                )
                .into(),
            name: vec![],
            task: None,
            conditions: vec![condition],
            effects: vec![effect, effect_2],
            constraints,
            subtasks: vec![],
            //subtasks: vec![subtask],
            cost: None,
        },
    };

    chronicles.push(chronicle_origin);

    for chronicle in &chronicles {
        Printer::print_chronicle(&chronicle.chronicle, &ctx.model)
    }

    Arc::new(FiniteProblem {
        model: ctx.model.clone(),
        origin: ctx.origin(),
        horizon: ctx.horizon(),
        chronicles,
    })
}

pub fn cst_fatom(f: f32) -> FAtom {
    FAtom::new(IAtom::from((f * TIME_SCALE.get() as f32) as i32), TIME_SCALE.get())
}

pub fn cst_iatom(i: i32) -> IAtom {
    IAtom::from(i)
}
