import csv
import subprocess
import re
import json
import os
import time
import gc
from pathlib import Path

try:
    import pyRAPL
    PYRAPL_AVAILABLE = True
except ImportError:
    PYRAPL_AVAILABLE = False

class AriesEnergyProfiler:
    def __init__(self, config_path):
        # Set project root from config or fallback to script's parent
        with open(config_path, 'r') as f:
            self.config = json.load(f)
        
        self.root_dir = Path(self.config.get('project_root', '/home/rahul/Desktop/aries')).resolve()
        
        # Resolve all paths relative to the project root
        self.base_input_dir = (self.root_dir / self.config['input_directory']).resolve()
        self.output_root = (self.root_dir / self.config['output_directory']).resolve()
        self.funcs_file = (self.root_dir / self.config['function_selection_file']).resolve()
        self.binary_path = (self.root_dir / self.config['binary_path']).resolve()
        
        # Sanity Check
        if not self.binary_path.exists():
            raise FileNotFoundError(f"Binary not found at {self.binary_path}")

        self.tracked_functions = self.load_functions()
        if PYRAPL_AVAILABLE:
            try: pyRAPL.setup()
            except: print("⚠️ RAPL Setup failed. Ensure you run with sudo.")

    def load_functions(self):
        if not self.funcs_file.exists(): return []
        with open(self.funcs_file, 'r') as f:
            return [line.strip().split('#')[0].strip() for line in f if line.strip()]

    def parse_perf(self, data_file):
        results = {}
        top_functions = [] 
        if not data_file.exists(): return results

        try:
            # Added --demangle and specific flags for Rust symbols
            cmd = f"perf report -i {data_file} --stdio --no-children --demangle -n"
            output = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.STDOUT)
            
            lines = output.splitlines()
            for line in lines:
                if "%" in line and "[" in line and len(top_functions) < 10:
                    top_functions.append(line.strip())

                for target in self.tracked_functions:
                    # Clean the target for a robust search (handles BinaryHeap::pop)
                    clean_target = target.replace("::", ".*")
                    if re.search(clean_target, line, re.IGNORECASE):
                        match = re.search(r'(\d+\.\d+)%', line)
                        if match:
                            percentage = float(match.group(1))
                            results[target] = results.get(target, 0) + percentage
            
            if not results:
                print("      🔍 Tracked functions not detected. Top 5 seen by perf:")
                for fn in top_functions[:5]: print(f"        {fn}")
                    
        except Exception as e:
            print(f"    [!] Perf Parsing error: {e}")
        return results
    
    def run_command(self, cmd, label="Aries", is_profile=False, perf_file=None):
        uj = 0
        # CRITICAL: Only use perf record if is_profile is True
        full_cmd = f"perf record -F 999 -g -o {perf_file} -- {cmd}" if is_profile else cmd

        try:
            if PYRAPL_AVAILABLE:
                meter = pyRAPL.Measurement(label)
                meter.begin()
                subprocess.run(full_cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=self.config.get('timeout', 400))
                meter.end()
                uj = sum(meter.result.pkg) if meter.result and meter.result.pkg else 0
            else:
                subprocess.run(full_cmd, shell=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=self.config.get('timeout', 400))
        except subprocess.TimeoutExpired:
            print(f"    [!] {label} TIMED OUT")
        
        gc.collect()
        return uj

    def profile_problem(self, domain_file, problem_path, csv_path, prob_dir):
        time.sleep(5) # Cooldown
        with open(csv_path, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['Rep', 'Total_uJ', 'Function', 'Percent', 'Func_uJ'])

            for rep in range(1, self.config['repetitions'] + 1):
                binary_cmd = f"{self.binary_path} {problem_path}"
                
                if rep == 1:
                    perf_data = prob_dir / "profile.data"
                    uj = self.run_command(binary_cmd, is_profile=True, perf_file=perf_data)
                    time.sleep(1)
                    breakdown = self.parse_perf(perf_data)
                    
                    if not breakdown:
                        writer.writerow([rep, uj, "NONE_DETECTED", 0, 0])
                    else:
                        for func, pct in breakdown.items():
                            writer.writerow([rep, uj, func, pct, (pct/100)*uj])
                    if perf_data.exists(): os.remove(perf_data)
                else:
                    uj = self.run_command(binary_cmd)
                    writer.writerow([rep, uj, "PHASE_TOTAL", 100, uj])
                
                f.flush()
                time.sleep(2)

    def execute(self):
        domains = [d for d in self.base_input_dir.iterdir() if d.is_dir()]
        for domain_path in domains:
            domain_file = domain_path / "domain.hddl"
            problems = sorted([p for p in domain_path.glob("*.hddl") if "domain" not in p.name.lower()])
            for problem_path in problems:
                prob_dir = self.output_root / domain_path.name / problem_path.stem
                prob_dir.mkdir(parents=True, exist_ok=True)
                print(f"[*] Profiling {domain_path.name} -> {problem_path.name}")
                self.profile_problem(domain_file, problem_path, prob_dir / f"{problem_path.stem}.csv", prob_dir)

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=str, required=True)
    AriesEnergyProfiler(parser.parse_args().config).execute()