#!/usr/bin/python3
# pylint: disable=redefined-outer-name
import sys
from pathlib import Path
from typing import IO, Optional

from up_planner import AriesLocal

UP_DIR = Path(__file__).parent.resolve() / "unified_planning"
if UP_DIR not in sys.path:
    sys.path.insert(0, UP_DIR.as_posix())

# pylint: disable=wrong-import-position,no-name-in-module
from unified_planning.io.pddl_reader import PDDLReader  # noqa: E402

DEFAULT_PORT = 2222


def plan(
    domain: str,
    problem: str,
    output: str = None,
    port: int = DEFAULT_PORT,
) -> None:
    def solve(stdout: Optional[IO[str]] = None) -> None:
        planner = AriesLocal(port, stdout, compilation=False)
        planner.solve(up_problem)

    up_problem = PDDLReader().parse_problem(domain, problem)
    if output:
        with open(output, mode="w", encoding="utf-8") as stdout:
            solve(stdout)
    else:
        solve()


if __name__ == "__main__":
    import getopt

    # Get the arguments from the command line and parse them
    domain, problem = sys.argv[1:3]
    output, port = None, DEFAULT_PORT
    try:
        opts, args = getopt.getopt(sys.argv[3:], "o:p:", ["output=", "port="])
    except getopt.GetoptError as err:
        print(err)
        sys.exit(2)
    for opt, arg in opts:
        if opt in ("-o", "--output"):
            output = arg
        elif opt in ("-p", "--port"):
            port = int(arg)

    # Start the planner
    plan(domain, problem, output, port)
