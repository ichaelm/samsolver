import re

import cpmpy as cp
from cpmpy.solvers.solver_interface import ExitStatus


def tokenize(text):
    tokens = []
    atoms = set()
    i = 0
    already_extracted_atoms = False
    extract_atoms = False
    while i < len(text):
        first_char = text[i]
        token_matcher = None
        extract_atoms = False
        if first_char.isalpha() or first_char == '$':
            token_matcher = r'([$a-zA-Z]+)'
            if not already_extracted_atoms:
                extract_atoms = True
        elif first_char.isdigit():
            token_matcher = r'([0-9]+)'
        elif first_char.isspace():
            i += 1
            continue
        else:
            token_matcher = r'([^$a-zA-Z0-9\s]+)'
        token = re.match(token_matcher, text[i:])[0]
        i += len(token)
        tokens.append(token)
        if extract_atoms:
            atoms.update(set(token) - set('$'))
            already_extracted_atoms = True
            extract_atoms = False
    return tokens, atoms

def use_op(left, right, op):
    if op == '>=':
        return left >= right
    elif op == '>':
        return left > right
    elif op == '<=':
        return left <= right
    elif op == '<':
        return left < right
    elif op == '=' or op == '==':
        return left == right
    elif op == '!=' or op == '<>':
        return left != right
    else:
        raise RuntimeError(f'Unsupported ast operator {op}')

def symbols_to_boolvars(symbols):
    return [cp.BoolVar(name=s) for s in symbols]

def connected_expr(leaf):
    innocence, symbols = (False, leaf[1:]) if leaf[0] == '$' else (True, leaf)
    if len(symbols) < 3:
        return True

    atoms = symbols_to_boolvars(symbols)
    tests_for_failure = []
    for center_idx in range(1, len(atoms)-1):
        left = atoms[:center_idx]
        center = atoms[center_idx]
        right = atoms[center_idx+1:]
        fail_test = None
        if innocence:
            fail_test = cp.any(left) & (~center) & cp.any(right)
        else:
            fail_test = (~cp.all(left)) & center & (~cp.all(right))
        tests_for_failure.append(fail_test)

    return ~cp.any(tests_for_failure)

def parity_expr(leaf, parity_str):
    innocence, symbols = (False, leaf[1:]) if leaf[0] == '$' else (True, leaf)
    atoms = symbols_to_boolvars(symbols)
    count_expr = None
    if innocence:
        count_expr = cp.sum(atoms)
    else:
        count_expr = len(atoms) - cp.sum(atoms)
    parity = 1 if (parity_str == 'odd') else 0
    return count_expr%2 == parity


def leaf_to_expr(leaf_text):
    first_char = leaf_text[0]
    if first_char.isalpha():
        return cp.sum(symbols_to_boolvars(leaf_text))
    elif first_char == '$':
        num_innocent = cp.sum(symbols_to_boolvars(leaf_text[1:]))
        num_atoms = len(leaf_text) - 1
        return num_atoms - num_innocent
    elif first_char.isdigit():
        return int(leaf_text)

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
    tuv>=w     If W is innocent, then at least one of TUV is.
    abc!=0
    abc!=2    There is an odd number of innocents among ABC (needs 2 lines).

"""

TIMEOUT_WARNING = """
Failed to solve: the current set of rules is too complex!
Try restarting with new rules referencing only the unknown people.
"""

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

def main():
    the_truth = cp.Model()
    all_atomics = set()  # Variable names added to the model so far
    known_facts = set()  # Results that have already been displayed
    try:
        print(WELCOME)
        while True:
            try:
                clue_text = enter_clue()
                tokens, atomics = tokenize(clue_text)
                if len(tokens) != 3:
                    raise TryAgain('Syntax error 1')
                left, op, right = tokens
                expr = None
                if op == 'is':
                    if right == 'connected':
                        expr = connected_expr(left)
                    elif right in ['odd', 'even']:
                        expr = parity_expr(left, right)
                    else:
                        raise TryAgain('Syntax error 2')

                else:
                    expr = use_op(leaf_to_expr(left), leaf_to_expr(right), op)
                all_atomics.update(atomics)


                the_truth += expr

                _ = the_truth.solve(time_limit=SOLVER_SECONDS)
                solver_status = the_truth.status()
                if solver_status.exitstatus == ExitStatus.UNSATISFIABLE:
                    raise Exit('No solution. Contradiction found.')
                if solver_status.exitstatus == ExitStatus.UNKNOWN:
                    raise Exit(TIMEOUT_WARNING)

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
