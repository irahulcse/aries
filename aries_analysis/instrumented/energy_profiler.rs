//! Energy profiling module for Aries planner
//! Measures energy consumption at function level using Intel RAPL

use std::fs::File;
use std::io::{self, Read, Write};
use std::time::Instant;
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    pub static ref GLOBAL_PROFILER: Mutex<Option<EnergyProfiler>> = 
        Mutex::new(Some(EnergyProfiler::new()));
}

pub struct EnergyProfiler {
    measurements: Vec<EnergyMeasurement>,
    start_time: Instant,
    max_energy_range: u64,
}

#[derive(Clone, Debug)]
pub struct EnergyMeasurement {
    pub component: String,
    pub function: String,
    pub timestamp_ns: u128,
    pub energy_uj: u64,
    pub duration_ns: u128,
}

impl EnergyProfiler {
    pub fn new() -> Self {
        let max_range = Self::read_max_energy_range().unwrap_or(262143328850);
        Self {
            measurements: Vec::new(),
            start_time: Instant::now(),
            max_energy_range: max_range,
        }
    }
    
    fn read_max_energy_range() -> io::Result<u64> {
        let mut file = File::open("/sys/class/powercap/intel-rapl/intel-rapl:0/max_energy_range_uj")?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents.trim().parse().unwrap_or(262143328850))
    }
    
    fn read_rapl_energy() -> io::Result<u64> {
        let mut file = File::open("/sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj")?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents.trim().parse().unwrap_or(0))
    }
    
    pub fn start_function(&self, component: &str, function: &str) -> FunctionGuard {
        FunctionGuard {
            component: component.to_string(),
            function: function.to_string(),
            start_energy: Self::read_rapl_energy().unwrap_or(0),
            start_time: Instant::now(),
            profiler_start: self.start_time,
            max_range: self.max_energy_range,
        }
    }
    
    pub fn record_measurement(&mut self, guard: FunctionGuard) {
        let end_energy = Self::read_rapl_energy().unwrap_or(0);
        let duration = guard.start_time.elapsed();
        
        let energy_consumed = if end_energy >= guard.start_energy {
            end_energy - guard.start_energy
        } else {
            // Handle RAPL counter overflow
            guard.max_range - guard.start_energy + end_energy
        };
        
        self.measurements.push(EnergyMeasurement {
            component: guard.component,
            function: guard.function,
            timestamp_ns: guard.profiler_start.elapsed().as_nanos(),
            energy_uj: energy_consumed,
            duration_ns: duration.as_nanos(),
        });
    }
    
    pub fn save_to_csv(&self, path: &str) -> io::Result<()> {
        let mut file = File::create(path)?;
        writeln!(file, "component,function,timestamp_ns,energy_uj,duration_ns")?;
        
        for m in &self.measurements {
            writeln!(
                file,
                "{},{},{},{},{}",
                m.component, m.function, m.timestamp_ns, m.energy_uj, m.duration_ns
            )?;
        }
        
        Ok(())
    }
    
    pub fn print_summary(&self) {
        let mut component_energy: HashMap<String, u64> = HashMap::new();
        let mut function_energy: HashMap<String, u64> = HashMap::new();
        let mut function_calls: HashMap<String, usize> = HashMap::new();
        
        for m in &self.measurements {
            *component_energy.entry(m.component.clone()).or_insert(0) += m.energy_uj;
            *function_energy.entry(m.function.clone()).or_insert(0) += m.energy_uj;
            *function_calls.entry(m.function.clone()).or_insert(0) += 1;
        }
        
        let total_energy: u64 = component_energy.values().sum();
        
        println!("\n{}", "=".repeat(80));
        println!("ENERGY PROFILING SUMMARY");
        println!("{}", "=".repeat(80));
        println!("\nTotal measurements: {}", self.measurements.len());
        println!("Total energy: {:.6} J", total_energy as f64 / 1_000_000.0);
        
        println!("\n{}", "=".repeat(80));
        println!("ENERGY BY COMPONENT");
        println!("{}", "=".repeat(80));
        let mut components: Vec<_> = component_energy.iter().collect();
        components.sort_by_key(|&(_, e)| std::cmp::Reverse(*e));
        
        println!("{:<20} {:>15} {:>15}", "Component", "Energy (J)", "Percentage");
        println!("{}", "-".repeat(80));
        for (comp, energy) in components {
            let energy_j = *energy as f64 / 1_000_000.0;
            let pct = (*energy as f64 / total_energy as f64) * 100.0;
            println!("{:<20} {:>15.6} {:>14.2}%", comp, energy_j, pct);
        }
        
        println!("\n{}", "=".repeat(80));
        println!("TOP 20 ENERGY-CONSUMING FUNCTIONS");
        println!("{}", "=".repeat(80));
        let mut functions: Vec<_> = function_energy.iter().collect();
        functions.sort_by_key(|&(_, e)| std::cmp::Reverse(*e));
        
        println!("{:<40} {:>12} {:>12} {:>12}", "Function", "Calls", "Total (J)", "Avg (J)");
        println!("{}", "-".repeat(80));
        for (func, energy) in functions.iter().take(20) {
            let energy_j = **energy as f64 / 1_000_000.0;
            let calls = function_calls.get(*func).unwrap_or(&0);
            let avg_j = energy_j / (*calls as f64);
            println!("{:<40} {:>12} {:>12.6} {:>12.6}", func, calls, energy_j, avg_j);
        }
        
        println!("\n{}", "=".repeat(80));
    }
}

pub struct FunctionGuard {
    component: String,
    function: String,
    start_energy: u64,
    start_time: Instant,
    profiler_start: Instant,
    max_range: u64,
}

impl Drop for FunctionGuard {
    fn drop(&mut self) {
        if let Ok(mut profiler) = GLOBAL_PROFILER.lock() {
            if let Some(prof) = profiler.as_mut() {
                let guard = FunctionGuard {
                    component: self.component.clone(),
                    function: self.function.clone(),
                    start_energy: self.start_energy,
                    start_time: self.start_time,
                    profiler_start: self.profiler_start,
                    max_range: self.max_range,
                };
                prof.record_measurement(guard);
            }
        }
    }
}

// Convenience macro for profiling
#[macro_export]
macro_rules! profile_function {
    ($component:expr, $function:expr) => {
        let _guard = $crate::energy_profiler::GLOBAL_PROFILER
            .lock()
            .ok()
            .and_then(|p| p.as_ref().map(|prof| prof.start_function($component, $function)));
    };
}

pub fn save_results(path: &str) {
    if let Ok(profiler) = GLOBAL_PROFILER.lock() {
        if let Some(prof) = profiler.as_ref() {
            prof.save_to_csv(path).ok();
            prof.print_summary();
        }
    }
}
