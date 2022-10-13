import sys 

# Use the local version of the UP in the `ext/up/unified_planning` git submodule
sys.path.insert(0, 'unified_planning')
sys.path.insert(0, 'ext/up/unified_planning')

import unified_planning
from unified_planning.shortcuts import *
from unified_planning.model.htn import *

import os 
dir_path = os.path.dirname(os.path.realpath(__file__))

instances_loc = "../../examples/scheduling/instances/jobshop"


instance = sys.argv[1] if len(sys.argv) > 1 else "ft06"
filename = f"{instances_loc}/{instance}.txt"

print(f"Solving {filename}")

with open(filename) as file:
    lines = file.readlines()

def ints(line):
    return list(map(int, line.rstrip().split()))
def int_matrix(lines)    :
    return list(map(ints, lines))

header = lines.pop(0)
sizes = ints(lines.pop(0))
num_jobs = sizes[0]
num_machines = sizes[1]

first_times_line = 1
last_times_line = first_times_line + num_jobs - 1
times = int_matrix(lines[first_times_line:last_times_line +1])
print("Times: ", times)


first_machine_line = last_times_line + 2
last_machine_line = first_machine_line + num_jobs - 1
machines = int_matrix(lines[first_machine_line:last_machine_line+1])
print("Machines: ", machines)


problem = unified_planning.model.htn.HierarchicalProblem(f'jobshop-{instance}')


Machine = UserType('Machine')
used = problem.add_fluent("used", BoolType(), default_initial_value=False, m=Machine)

machine_objects =[problem.add_object(f"m{i}", Machine) for i in range(1, num_machines+1)]

tasks = []

for j in range(num_jobs):
    tasks_of_job = []
    tasks.append(tasks_of_job)
    for t in range(num_machines):
        machine = machine_objects[machines[j][t] - 1]
        act = DurativeAction(f"t_{j}_{t}")
        act.set_fixed_duration(times[j][t])
        act.add_condition(StartTiming(), Not(used(machine)))
        act.add_condition(LeftOpenTimeInterval(StartTiming(), EndTiming()), used(machine))
        act.add_effect(StartTiming(), used(machine), True)
        act.add_effect(EndTiming(), used(machine), False)
        
        problem.add_action(act)
        task = Subtask(act, ident=act.name)
        problem.task_network.add_subtask(task)
        if len(tasks_of_job) > 0:
            prev_in_job = tasks_of_job[-1]
            problem.task_network.set_strictly_before(prev_in_job, task)
        tasks_of_job.append(task)


problem.add_quality_metric(unified_planning.model.metrics.MinimizeMakespan())

# print(problem)

# ===== Aries specific handling ========


def export_problem(problem, path):
    import os
    from unified_planning.grpc.proto_writer import ProtobufWriter
    with open(path, "wb") as f:
        writer = ProtobufWriter()
        data = writer.convert(problem)
        f.write(data.SerializeToString())

from up_planner import AriesLocal, cost

def plan(problem, expected_cost=None):
    #print(problem)
    print(f"\n==== {problem.name} ====")
    def callback(intermediate_result):
        if intermediate_result.plan:
            print("New plan with cost: ", float(cost(problem, intermediate_result.plan)))
    result = planner.solve(problem, callback)

    print("Answer: ", result.status)
    if result.plan:
        for start, action, duration in result.plan.timed_actions:
            if duration:
                print("%s: %s [%s]" % (float(start), action, float(duration)))
            else:
                print("%s: %s" % (float(start), action))
        # c = cost(problem, result.plan)
        # expected = f"(expected: {expected_cost})" if expected_cost is not None else ""
        # print("\nCost: ", c, expected)
        # assert expected_cost is None or c == expected_cost


export_problem(problem, f"/tmp/jobshop-{instance}.up")



planner = AriesLocal(port=2222)

plan(problem, expected_cost=None)
