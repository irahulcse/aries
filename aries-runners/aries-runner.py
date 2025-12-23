import csv
import subprocess
import re
import json
import os
from pathlib import Path
import pyRAPL

class AriesEnergyProfiler:
    def __init__(self, config_path):
        self.script_dir= Path(__file__).parent.resolve()
        print(f"[*] Loading config: {config_path}")
        with open(config_path, 'r') as f:
            self.config = json.load(f)
        
        # Default path: /home/rahul/Desktop/aries/benchmarks/domains
        self.base_input_dir = (self.script_dir / self.config['input_directory']).resolve()
        self.output_root = (self.script_dir / self.config['output_directory']).resolve()
        self.funcs_file = (self.script_dir / self.config['function_selection_file']).resolve()
        self.binary_path = (self.script_dir / self.config['binary_path']).resolve()
        
        self.tracked_functions = self.load_functions()
        pyRAPL.setup()
        print(f"[*] Base Benchmarks Path: {self.base_input_dir}")

    def load_functions(self):
        with open(self.funcs_file, 'r') as f: # Use the resolved self.funcs_file
            return [line.strip() for line in f if line.strip() and not line.startswith('#')]

    def run_command(self, cmd):
        meter = pyRAPL.Measurement("Aries")
        meter.begin()
        # Keep stderr visible to catch Valgrind overflows
        subprocess.run(cmd, shell=True, stdout=subprocess.DEVNULL)
        meter.end()
        return sum(meter.result.pkg)

    def get_breakdown(self, callgrind_file):
        results = {}
        try:
            output = subprocess.check_output(f"callgrind_annotate --auto=yes {callgrind_file}", shell=True, text=True)
            total_match = re.search(r'([\d,]+)\s+\(100\.0%\)\s+PROGRAM TOTALS', output)
            if not total_match: return {}
            total_instr = float(total_match.group(1).replace(',', ''))

            for line in output.splitlines():
                for func in self.tracked_functions:
                    if func in line:
                        match = re.search(r'^\s*([\d,]+)', line)
                        if match:
                            instr_count = float(match.group(1).replace(',', ''))
                            results[func] = results.get(func, 0) + (instr_count / total_instr * 100)
        except Exception as e:
            print(f"    [!] Parsing error: {e}")
        return results

    def execute(self):
        # Scan for domain folders under benchmarks/domains/
        domains = [d for d in self.base_input_dir.iterdir() if d.is_dir()]
        print(f"[*] Found {len(domains)} domains to process.")

        for domain_path in domains:
            domain_name = domain_path.name
            # Find all HDDL problems in this domain
            problems = [p for p in domain_path.glob("*.hddl") if "domain" not in p.name.lower()]
            
            if not problems:
                continue

            print(f"\n=== Processing Domain: {domain_name} ({len(problems)} problems) ===")

            for problem_path in problems:
                # Structure: output/DomainName/ProblemName/
                prob_dir = self.output_root / domain_name / problem_path.stem
                prob_dir.mkdir(parents=True, exist_ok=True)
                csv_path = prob_dir / f"{problem_path.stem}.csv"
                
                print(f"  > Problem: {problem_path.name}")
                self.profile_problem(problem_path, csv_path, prob_dir)

    def profile_problem(self, problem_path, csv_path, prob_dir):
        with open(csv_path, 'w', newline='') as f:
            writer = csv.writer(f)
            writer.writerow(['Rep', 'Total_uJ', 'Function', 'Percent', 'Func_uJ'])

            for rep in range(1, self.config['repetitions'] + 1):
                # Force single worker for profiling stability
                binary = f"{self.config['binary_path']}"
                
                if rep == 1:
                    cg_file = prob_dir / "profile.callgrind"
                    cmd = (f"valgrind --tool=callgrind --max-stackframe=20000000 "
                           f"--main-stacksize=20000000 --run-libc-freeres=no "
                           f"--callgrind-out-file={cg_file} {binary} {problem_path}")
                    
                    uj = self.run_command(cmd)
                    breakdown = self.get_breakdown(cg_file)
                    
                    if not breakdown:
                        writer.writerow([rep, uj, "NONE_DETECTED", 0, 0])
                    for func, pct in breakdown.items():
                        writer.writerow([rep, uj, func, pct, (pct/100)*uj])
                else:
                    uj = self.run_command(f"{binary} {problem_path}")
                    writer.writerow([rep, uj, "PHASE_TOTAL", 100, uj])
                
                if rep % 10 == 0:
                    print(f"    - Finished Rep {rep}")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', type=str, required=True)
    args = parser.parse_args()
    AriesEnergyProfiler(args.config).execute()