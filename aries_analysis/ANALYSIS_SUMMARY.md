# Aries Function-Level Analysis Summary

Generated: Wed Dec 17 10:15:07 AM CET 2025

## Directory Structure

```
./aries_analysis/
├── functions/              # Extracted function signatures
├── call_graphs/            # Function call graphs
├── instrumented/           # Generated instrumentation code
│   └── energy_profiler.rs
├── key_functions.txt       # Functions to instrument
├── INSTRUMENTATION_GUIDE.md
└── ANALYSIS_SUMMARY.md     # This file
```

## Next Steps

1. **Review key functions**: Edit `key_functions.txt` to prioritize functions
2. **Add profiler module**: Copy `instrumented/energy_profiler.rs` to Aries source
3. **Instrument code**: Follow `INSTRUMENTATION_GUIDE.md`
4. **Build and run**: Rebuild Aries and run on benchmarks
5. **Analyze results**: Use provided Python scripts

## Key Files to Instrument

See `key_functions.txt` for the complete list.

### High Priority (Component-level):
- Parsing: parse_pddl_domain, parse_pddl_problem
- Preprocessing: preprocess, remove_unusable_effects, lift_predicates
- Decomposition: populate_with_task_network
- Solving: solve, propagate, make_decision

### Medium Priority (Algorithm-level):
- Constraint propagation functions
- Search and backtracking
- Conflict analysis

### Low Priority (Helper functions):
- Individual propagators
- Data structure operations

## Measurement Considerations

- **Overhead**: Profiling adds ~10-50 microseconds per function call
- **Accuracy**: RAPL has ~1ms sampling resolution
- **Coverage**: Instrument only critical path functions first
- **Validation**: Compare total energy with external measurements

## Analysis Scripts

1. `analyze_function_energy.py` - Basic analysis
2. `component_attribution_analysis.py` - Detailed component breakdown
3. Jupyter notebook - Interactive exploration

## References

- PLANERGYM Paper: Function-level energy profiling methodology
- Intel RAPL: https://www.intel.com/rapl
- Aries Source: https://github.com/plaans/aries
