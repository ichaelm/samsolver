import ast
import re

import cpmpy as cp
from cpmpy.solvers.solver_interface import ExitStatus


def use_op(left, right, op):
    if isinstance(op, ast.GtE):
        return left >= right
    elif isinstance(op, ast.Gt):
        return left > right
    elif isinstance(op, ast.LtE):
        return left <= right
    elif isinstance(op, ast.Lt):
        return left < right
    elif isinstance(op, ast.Eq):
        return left == right
    elif isinstance(op, ast.NotEq):
        return left != right
    else:
        raise RuntimeError(f'Unsupported ast operator {op}')

def symbols_to_boolvars(symbols):
    return [cp.BoolVar(name=s) for s in symbols]

def combinations_expr(symbols, threshold, op):
    left_expr = cp.sum(symbols_to_boolvars(symbols))
    right_expr = threshold
    return use_op(left_expr, right_expr, op)

def comparison_expr(left_symbols, right_symbols, op):
    left_expr = cp.sum(symbols_to_boolvars(left_symbols))
    right_expr = cp.sum(symbols_to_boolvars(right_symbols))
    return use_op(left_expr, right_expr, op)

def find_known_facts(model, atomics):
    for atom in atomics:
        if_true = model.copy().add(cp.BoolVar(name=atom))
        if not if_true.solve():
            yield f'{atom.upper()} is a criminal.'
        else:
            if_false = model.copy().add(~cp.BoolVar(name=atom))
            if not if_false.solve():
                yield f'{atom.upper()} is innocent.'


WELCOME = """Starting a new game. Type "h" for help or "q" for quit."""
HELP = """
This program is a solver for http://cluesbysam.com

Enter the information you're given, one clue at a time. Each piece of
information you receive may end up as more than one clue in this program.

Each clue uses one of these operators:
    =         equals
    !=        does not equal
    >         is greater than
    <         is less than
    >=        is greater than or equal to
    <=        is less than or equal to

Each side of the operator represents a number of INNOCENT people.

When a side has multiple letters, addition is implied.

Examples:
    a = 1     A is innocent
    b = 0     B is a criminal
    cd = 1    C and D are opposites
    ef = 2    E and F are both innocent
    gh > 0    G and H can't both be criminals
    ijk>lmn   There are more innocents among I, J, and K than L, M, and N.
    pq<=rs    There are at least as many criminals among RS as among PQ.
    tuv>w     If W is innocent, then at least one of TUV is.
    abc!=0
    abc!=2    There is an odd number of innocents among ABC (needs 2 lines).

"""

TIMEOUT_WARNING = """Warning: the current set of rules is too complex!
Try restarting with new rules referencing only the unknown people."""

SOLVER_SECONDS = 1

class TryAgain(Exception):
    def __init__(self, message=None):
        self.message = message
        super().__init__(self.message)

class Exit(Exception):
    def __init__(self, message=None):
        self.message = message
        super().__init__(self.message)

def enter_clue():
    clue_text = input("Enter a clue: ").strip().lower()
    if clue_text in ('h', 'help'):
        raise TryAgain(HELP)
    if clue_text in ('q', 'quit'):
        raise Exit("Goodbye!")
    return clue_text

def text_to_ast(text):
    clue_text = re.sub(r"\b=\b", "==", text)
    tree = ast.parse(clue_text, mode="eval").body
    if not isinstance(tree, ast.Compare):
        raise TryAgain("Only comparison expressions are allowed.")
    if len(tree.ops) != 1:
        raise TryAgain("Only one comparison at a time is allowed.")

def ast_to_cpm_expr(tree):
    atomics = set()
    comparison_op = tree.ops[0]
    left = tree.left
    right = tree.comparators[0]
    if not isinstance(left, ast.Name):
        raise TryAgain("The left side of the comparison must be a string of letters.")
    if not (isinstance(right, ast.Constant) or isinstance(left, ast.Name)):
        raise TryAgain("The right side of the comparison must be a constant or a string of letters.")
    atomics.update(left.id)
    expr = None
    if isinstance(right, ast.Constant):
        expr = combinations_expr(left.id, right.value, comparison_op)
    else:
        atomics.update(right.id)
        expr = comparison_expr(left.id, right.id, comparison_op)
    return expr, atomics

def main():
    the_truth = cp.Model()
    all_atomics = set()  # Variable names added to the model so far
    known_facts = set()  # Results that have already been displayed
    try:
        print(WELCOME)
        while True:
            try:
                clue_text = enter_clue()
                tree = text_to_ast(clue_text)
                expr, atomics = ast_to_cpm_expr(tree)
                all_atomics.update(atomics)

                the_truth += expr

                _ = the_truth.solve(time_limit=SOLVER_SECONDS)
                solver_status = the_truth.status()
                if solver_status.exitstatus == ExitStatus.UNSATISFIABLE:
                    raise Exit('No solution. Contradiction found.')
                if solver_status.exitstatus == ExitStatus.UNKNOWN:
                    print(TIMEOUT_WARNING)

                new_known_facts = set(find_known_facts(the_truth, all_atomics))
                added_facts = new_known_facts - known_facts
                known_facts = new_known_facts

                for fact in added_facts:
                    print(fact)

            except TryAgain as e:
                print(e.message)
                continue
    except KeyboardInterrupt:
        pass
    except Exit as e:
        print(e.message)
        pass


if __name__ == "__main__":
    main()
