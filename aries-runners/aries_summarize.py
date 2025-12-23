import pandas as pd
from pathlib import Path
import os

def summarize_aries_data(output_dir="./output_aries_results"):
    base_path = Path(output_dir)
    summary_data = []

    # 1. Find all CSV files in the nested structure
    csv_files = list(base_path.glob("**/*.csv"))
    
    if not csv_files:
        print(f"[!] No CSV files found in {base_path}")
        return

    print(f"[*] Aggregating data from {len(csv_files)} problems...")

    for csv_path in csv_files:
        try:
            # Extract domain and problem names from the path
            problem_name = csv_path.stem
            domain_name = csv_path.parent.parent.name
            
            df = pd.read_csv(csv_path)

            # 2. Separate Native Reps (Energy) from Profiling Rep (Functions)
            # Native reps are where Function == "PHASE_TOTAL"
            native_reps = df[df['Function'] == 'PHASE_TOTAL']
            profiling_rep = df[df['Rep'] == 1]

            if native_reps.empty:
                continue

            # 3. Calculate Energy Statistics (converted to Joules for readability)
            mean_uj = native_reps['Total_uJ'].mean()
            std_uj = native_reps['Total_uJ'].std()
            mean_j = mean_uj / 1_000_000
            
            # 4. Extract Function Breakdown
            func_breakdown = {}
            for _, row in profiling_rep.iterrows():
                if row['Function'] != "PHASE_TOTAL":
                    func_breakdown[row['Function']] = row['Percent']

            # 5. Build the result row
            entry = {
                'Domain': domain_name,
                'Problem': problem_name,
                'Avg_Energy_J': round(mean_j, 4),
                'Std_Dev_J': round(std_uj / 1_000_000, 4) if not pd.isna(std_uj) else 0,
                'Sample_Size': len(native_reps)
            }
            # Add function columns
            for func, pct in func_breakdown.items():
                entry[f"Func_{func}_%"] = round(pct, 2)

            summary_data.append(entry)
        except Exception as e:
            print(f" [!] Error processing {csv_path}: {e}")

    # 6. Create Master DataFrame and Export
    master_df = pd.DataFrame(summary_data)
    
    # Sort by Domain and then Energy
    master_df = master_df.sort_values(['Domain', 'Avg_Energy_J'])
    
    # Save to Excel and CSV
    master_df.to_csv("aries_master_summary.csv", index=False)
    print("\n" + "="*50)
    print("SUCCESS: Summary created as 'aries_master_summary.csv'")
    print("="*50)
    print(master_df.to_string(index=False))

if __name__ == "__main__":
    # Ensure pandas is installed: pip install pandas
    summarize_aries_data()