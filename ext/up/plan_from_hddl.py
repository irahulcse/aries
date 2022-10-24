#!/usr/bin/python3
# pylint: disable=redefined-outer-name
from __future__ import annotations

import sys
from pathlib import Path
from typing import IO, Optional

import click
from up_planner import AriesLocal

UP_DIR = Path(__file__).parent.resolve() / "unified_planning"
if UP_DIR not in sys.path:
    sys.path.insert(0, UP_DIR.as_posix())

# pylint: disable=wrong-import-position,no-name-in-module
from unified_planning.io.pddl_reader import PDDLReader  # noqa: E402

DEFAULT_PORT = 2222


@click.command(context_settings=dict(help_option_names=["-h", "--help"]))
@click.argument("domain", type=str)
@click.argument("problem", type=str)
@click.option("-o", "--output", type=str, help="Output file for the planner.")
@click.option(
    "-p",
    "--port",
    type=int,
    default=DEFAULT_PORT,
    help="Port used by the planner.",
    show_default=True,
)
def plan(
    domain: str,
    problem: str,
    output: str | None,
    port: int = DEFAULT_PORT,
) -> None:
    """
    Parses the given HDDL files and solves the associated problem.
    """

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
    plan()  # pylint: disable=no-value-for-parameter
