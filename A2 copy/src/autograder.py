#!/usr/bin/env python3
"""
Refactored Autograder for CSP Futoshiki Assignments.

Usage:
  python autograder.py
  python autograder.py --verbose (for more detailed output)
  python autograder.py --test example_csp_test (to run a specific test)

Implementing tests:
To add a new test, create a new test function that takes a propagator 
function or a model as an argument. Add the test function to the `tests` list at
the end of the script. The test must return a tuple of three values:
    - score (int): 1 if the test passed, 0 otherwise
    - details (str): a string with additional information about the test
    - max_score (int): the maximum score that can be achieved in this test

The test function should be of the form:
    def my_test(propagator, name=""):
        # Your test code here
        return score, details, max_score
"""

import argparse
import signal
import traceback
import itertools
import io
import contextlib

import cspbase
from propagators import prop_FC
import propagators as soln_propagators

TIMEOUT = 60

#######################################
# UTILITIES & TIMEOUTS
#######################################
class TimeoutException(Exception):
    """Raised when time is up."""
    pass

def _timeout_handler(signum, frame):
    raise TimeoutException("Timeout occurred")

def set_timeout(seconds):
    signal.signal(signal.SIGALRM, _timeout_handler)
    signal.alarm(seconds)

def reset_timeout():
    """Disable alarm."""
    signal.alarm(0)

def contains_list(lst):
    return any(isinstance(e, list) for e in lst)

def sort_innermost_lists(lst):
    """
    Sort the innermost lists in a list-of-lists-of-lists recursively.
    Used for comparing nested lists ignoring order in the innermost layer.
    """
    if not isinstance(lst, list):
        return
    elif contains_list(lst):
        for e in lst:
            sort_innermost_lists(e)
    else:
        lst.sort()

def log(msg, verbose):
    if verbose:
        print(msg)

def w_eq_sum_x_y_z(values):
    w, x, y, z = values
    return w == (x + y + z)


#######################################
# TEST FUNCTIONS
#######################################
def example_csp_test(propagator, name=""):
    x = cspbase.Variable('X', [1, 2, 3])
    y = cspbase.Variable('Y', [1, 2, 3])
    z = cspbase.Variable('Z', [1, 2, 3])
    w = cspbase.Variable('W', [1, 2, 3, 4])

    c1 = cspbase.Constraint('C1', [x, y, z])
    # c1 is constraint x == y + z. Below are all of the satisfying tuples
    c1.add_satisfying_tuples([[2, 1, 1], [3, 1, 2], [3, 2, 1]])

    c2 = cspbase.Constraint('C2', [w, x, y, z])
    # c2 is constraint w == x + y + z.
    var_doms = []
    for v in [w, x, y, z]:
        var_doms.append(v.domain())

    sat_tuples = []
    for t in itertools.product(*var_doms):
        if w_eq_sum_x_y_z(t):
            sat_tuples.append(t)

    c2.add_satisfying_tuples(sat_tuples)

    simple_csp = cspbase.CSP("SimpleEqs", [x, y, z, w])
    simple_csp.add_constraint(c1)
    simple_csp.add_constraint(c2)

    btracker = cspbase.BT(simple_csp)
    # btracker.trace_on()

    set_timeout(TIMEOUT)
    btracker.bt_search(propagator)
    curr_vars = simple_csp.get_all_vars()
    answer = [[2], [1], [1], [4]]
    var_vals = [x.cur_domain() for x in curr_vars]
    reset_timeout()
    if var_vals != answer:
        details = "Failed while testing a propagator (%s): variable domains don't match expected results" % name
        return 0, details, 1
    else:
        return 1, "", 1

def test_prop_FC(propagator=None, name=""):
    '''
    Test the Forward Checking propagator using a simple CSP example.

    Arguments:
        propagator: The propagator function to test (prop_FC).
        name (str): Optional name for the test case.

    Returns:
        tuple: (int, str, int) representing (test success: 0/1, details: str, total points: int)
    '''
    X = cspbase.Variable('X', [1, 2])
    Y = cspbase.Variable('Y', [1, 2])

    constraint = cspbase.Constraint("X!=Y", [X, Y])
    constraint.add_satisfying_tuples([(1, 2), (2, 1)])

    simple_csp = cspbase.CSP("SimpleFC", [X, Y])
    simple_csp.add_constraint(constraint)

    # Explicitly assign X = 1
    X.assign(1)

    # Explicitly run forward checking propagation step
    fc_result, pruned = propagator(simple_csp, X)

    # After assigning X=1, Y's domain should prune value 1
    expected_X_domain = [1]  # assigned value
    expected_Y_domain = [2]  # value 1 should be pruned

    actual_domains = [X.cur_domain(), Y.cur_domain()]
    expected_domains = [expected_X_domain, expected_Y_domain]

    if not fc_result or actual_domains != expected_domains:
        details = f"Failed test '{name}': expected domains {expected_domains}, got {actual_domains}"
        return 0, details, 1
    else:
        return 1, "", 1

def jha_test_prop_FC(propagator_module, name="prop_FC_test"):
    """
    Test the forward checking propagator (prop_FC).
    Create a simple binary CSP with the constraint X != Y.
    After assigning X = 1 and running FC, Y's domain should not contain 1.
    """
    try:
        fc = propagator_module.prop_FC
    except AttributeError:
        return 0, "prop_FC not implemented in propagators", 1

    X = cspbase.Variable('X', [1, 2, 3])
    Y = cspbase.Variable('Y', [1, 2, 3])
    simpleCSP = cspbase.CSP("FC_Test", [X, Y])
    neq_constraint = cspbase.Constraint("X != Y", [X, Y])
    allowed = [(x, y) for x in X.domain() for y in Y.domain() if x != y]
    neq_constraint.add_satisfying_tuples(allowed)
    simpleCSP.add_constraint(neq_constraint)

    X.assign(1)
    ok, pruned = fc(simpleCSP, X)
    if not ok:
        return 0, "prop_FC detected a dead-end unexpectedly", 1
    if 1 in Y.cur_domain():
        details = ("prop_FC failed to prune value 1 from Y's domain: %s" % Y.cur_domain())
        return 0, details, 1
    return 1, "", 1

import cspbase

def test_prop_FC_no_pruning(propagator=None, name=""):
    '''
    Test Forward Checking with a CSP example that shouldn't prune any domains.

    Arguments:
        propagator: The propagator function (prop_FC).
        name (str): Optional name for the test case.

    Returns:
        tuple: (int, str, int)
    '''
    A = cspbase.Variable('A', [1, 2])
    B = cspbase.Variable('B', [3, 4])

    constraint = cspbase.Constraint("A<B", [A, B])
    constraint.add_satisfying_tuples([(1,3), (1,4), (2,3), (2,4)])

    no_prune_csp = cspbase.CSP("NoPruneFC", [A, B])
    no_pruning_csp = cspbase.CSP("NoPrune", [A, B])
    no_prune_csp = cspbase.CSP("NoPruneCSP", [A, B])
    no_prune_csp.add_constraint(constraint)

    A.assign(1)
    result, pruned = propagator(no_prune_csp, A)

    expected_domains = [[1], [3, 4]]
    var_domains = [var.cur_domain() for var in no_prune_csp.get_all_vars()]

    if not result or var_domains != expected_domains:
        details = f"Failed test '{name}': expected domains {expected_domains}, got {var_domains}"
        return 0, details, 1

    return 1, "", 1

def test_prop_FC_DWO(propagator=None, name=""):
    '''
    Test prop_FC for correctly detecting domain wipe-out.

    Arguments:
        propagator: The propagator function to test.
        name (str): Optional name for the test case.

    Returns:
        tuple: (int, str, int)
    '''
    X = cspbase.Variable('X', [1])
    Y = cspbase.Variable('Y', [1])

    constraint = cspbase.Constraint("X!=Y", [X, Y])
    constraint.add_satisfying_tuples([])  # No allowed tuples

    dwo_csp = cspbase.CSP("DWOCSP", [X, Y])
    dwo_csp.add_constraint(constraint)

    X.assign(1)
    result, pruned = propagator(dwo_csp, X)

    if result is not False:
        details = f"Failed test '{name}': Domain wipe-out not detected when it should have been"
        return 0, details, 1

    return 1, "", 1

def jha_test_prop_GAC(propagator_module, name="prop_GAC_test"):
    """
    Test the generalized arc consistency propagator (prop_GAC).
    Create a simple binary CSP with the constraint X != Y.
    After assigning X = 1 and running GAC, Y's domain should not contain 1.
    """
    try:
        gac = propagator_module.prop_GAC
    except AttributeError:
        return 0, "prop_GAC not implemented in propagators", 1

    X = cspbase.Variable('X', [1, 2, 3])
    Y = cspbase.Variable('Y', [1, 2, 3])
    simpleCSP = cspbase.CSP("GAC_Test", [X, Y])
    neq_constraint = cspbase.Constraint("X != Y", [X, Y])
    allowed = [(x, y) for x in X.domain() for y in Y.domain() if x != y]
    neq_constraint.add_satisfying_tuples(allowed)
    simpleCSP.add_constraint(neq_constraint)

    X.assign(1)
    ok, pruned = gac(simpleCSP, X)
    if not ok:
        return 0, "prop_GAC detected a dead-end unexpectedly", 1
    if 1 in Y.cur_domain():
        details = ("prop_GAC failed to prune value 1 from Y's domain: %s" % Y.cur_domain())
        return 0, details, 1
    return 1, "", 1

def test_GAC_simple(propagator, name=""):
    '''Simple CSP, no pruning necessary.'''
    X = cspbase.Variable('X', [1])
    Y = cspbase.Variable('Y', [1])

    c = cspbase.Constraint("X=Y", [X, Y])
    c.add_satisfying_tuples([(1, 1)])

    csp = cspbase.CSP("SimpleGAC", [X, Y])
    csp.add_constraint(c)

    result, pruned = propagator(csp)

    if result and not pruned:
        return 1, "", 1
    return 0, "Simple test failed", 1


def test_GAC_prune(propagator, name=""):
    '''CSP requiring pruning but no domain wipe-out.'''
    X = cspbase.Variable('X', [1, 2])
    Y = cspbase.Variable('Y', [1, 2])

    c = cspbase.Constraint("X!=Y", [X, Y])
    c.add_satisfying_tuples([(1, 2), (2, 1)])

    csp = cspbase.CSP("GACPrune", [X, Y])
    csp.add_constraint(c)

    X.assign(1)
    result, pruned = propagator(csp, X)

    if result and (Y, 1) in pruned and Y.cur_domain() == [2]:
        return 1, "", 1
    return 0, "Prune test failed", 1


def test_GAC_domain_wipeout(propagator, name=""):
    '''CSP that should detect a domain wipe-out.'''
    X = cspbase.Variable('X', [1])
    Y = cspbase.Variable('Y', [2])

    c = cspbase.Constraint("X=Y", [X, Y])
    c.add_satisfying_tuples([])

    csp = cspbase.CSP("GACDWO", [X, Y])
    csp.add_constraint(c)

    result, pruned = propagator(csp)

    if not result:
        return 1, "", 1
    return 0, "Domain wipeout test failed", 1


def test_GAC_chain_reaction(propagator, name=""):
    '''CSP testing chain reactions of pruning.'''
    X = cspbase.Variable('X', [1, 2])
    Y = cspbase.Variable('Y', [1, 2])
    Z = cspbase.Variable('Z', [1, 2])

    c1 = cspbase.Constraint("X!=Y", [X, Y])
    c1.add_satisfying_tuples([(1, 2)])

    c2 = cspbase.Constraint("Y!=Z", [Y, Z])
    c2.add_satisfying_tuples([(2, 1)])

    csp = cspbase.CSP("GACChainReaction", [X, Y, Z])
    csp.add_constraint(c1)
    csp.add_constraint(c2)

    result, pruned = propagator(csp)

    expected_domains = [[1], [2], [1]]
    domains = [var.cur_domain() for var in csp.get_all_vars()]

    if result and domains == expected_domains:
        return 1, "", 1
    return 0, "Chain reaction test failed", 1

def jha_test_ord_mrv(propagator, name="ord_mrv_test"):
    """
    Test the ord_mrv heuristic. Create a CSP with variables having different domain sizes.
    The variable with the smallest domain (here, variable 'E' with domain [1]) should be selected.
    """
    try:
        import propagators as student_propagators
        ord_mrv = student_propagators.ord_mrv
    except ImportError:
        return 0, "propagators module not found", 1

    a = cspbase.Variable('A', [1, 2, 3, 4, 5])
    b = cspbase.Variable('B', [1, 2, 3, 4])
    c = cspbase.Variable('C', [1, 2])
    d = cspbase.Variable('D', [1, 2, 3])
    e = cspbase.Variable('E', [1])
    simpleCSP = cspbase.CSP("SimpleMRV", [a, b, c, d, e])

    chosen = ord_mrv(simpleCSP)
    # Handle if the student accidentally returns a tuple.
    if isinstance(chosen, tuple):
        chosen = chosen[0]
    if isinstance(chosen, bool):
        return 0, "ord_mrv returned a bool; expected a Variable", 1
    if chosen is None:
        return 0, "ord_mrv returned None", 1
    elif chosen.name == "E":
        return 1, "", 1
    else:
        details = ("ord_mrv returned variable %s; expected 'E'" % chosen.name)
        return 0, details, 1

def test_ord_mrv_simple(propagator, name="ord_mrv_simple"):
    try:
        mrv = propagator.ord_mrv
    except AttributeError:
        return 0, "ord_mrv not implemented in propagators", 1

    X = cspbase.Variable('X', [1, 2])
    Y = cspbase.Variable('Y', [1])

    csp = cspbase.CSP("SimpleMRV", [X, Y])
    chosen = propagator.ord_mrv(csp)

    if chosen != Y:
        return 0, f"{name} failed: expected variable Y, got {chosen}", 1
    return 1, "", 1


def test_ord_mrv_all_assigned(propagator, name="ord_mrv_all_assigned"):
    X = cspbase.Variable('X', [1])
    X.assign(1)

    csp = cspbase.CSP("AllAssigned", [X])
    chosen = propagator.ord_mrv(csp)

    if chosen is not None:
        return 0, f"{name} failed: expected None, got {chosen.name}", 1

    return 1, "", 1


def test_ord_mrv_tie_break(propagator, name="ord_mrv_tie_break"):
    X = cspbase.Variable('X', [1, 2])
    Y = cspbase.Variable('Y', [1, 2])

    csp = cspbase.CSP("TieBreak", [X, Y])
    chosen = propagator.ord_mrv(csp)

    if chosen not in [X, Y]:
        return 0, f"{name} failed: tie-breaking chose unexpected variable {chosen.name}", 1

    return 1, "", 1


def test_ord_mrv_empty_csp(propagator, name="ord_mrv_empty"):
    csp = cspbase.CSP("Empty", [])
    chosen = propagator.ord_mrv(csp)

    if chosen is not None:
        return 0, f"{name} failed: expected None, got {chosen.name}", 1

    return 1, "", 1


def jha_futoshiki_model1_solvable_test(propagator, name="futoshiki_model1_solvable_test"):
    """
    Test futoshiki_csp_model_1 on a solvable board.
    Board (3x3):
      [1, '<', 0, '.', 0]
      [0, '.', 0, '.', 2]
      [2, '.', 0, '>', 0]
    Expected solution (row-major): [1, 2, 3, 3, 1, 2, 2, 3, 1]
    """
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    board = [
        [1, '<', 0, '.', 0],
        [0, '.', 0, '.', 2],
        [2, '.', 0, '>', 0]
    ]
    expected_solution = [1, 2, 3, 3, 1, 2, 2, 3, 1]

    result = student_models.futoshiki_csp_model_1(board)
    if result is None:
        return 0, "futoshiki_csp_model_1 returned None", 1
    csp, var_array = result

    bt_solver = cspbase.BT(csp)
    set_timeout(TIMEOUT)
    bt_solver.bt_search(propagator)
    reset_timeout()

    sol = [var.get_assigned_value() for row in var_array for var in row]
    if sol == expected_solution:
        return 1, "", 1
    else:
        details = ("Expected solution %s, but got %s" %
                   (expected_solution, sol))
        return 0, details, 1

def futoshiki_model1_unsolvable_test(propagator, name="futoshiki_model1_unsolvable_test"):
    """
    Test futoshiki_csp_model_1 on an unsolvable board.
    Board (3x3):
      [1, '>', 0, '.', 3]
      [0, '.', 0, '.', 0]
      [3, '<', 0, '.', 1]
    Expected: the board remains unsolved (at least one variable unassigned).
    """
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    board = [
        [1, '>', 0, '.', 3],
        [0, '.', 0, '.', 0],
        [3, '<', 0, '.', 1]
    ]
    result = student_models.futoshiki_csp_model_1(board)
    if result is None:
        return 0, "futoshiki_csp_model_1 returned None", 1
    csp, var_array = result

    bt_solver = cspbase.BT(csp)
    set_timeout(TIMEOUT)
    bt_solver.bt_search(propagator)
    reset_timeout()

    # At least one variable should remain unassigned.
    incomplete = any(var.get_assigned_value() is None for row in var_array for var in row)
    if incomplete:
        return 1, "", 1
    else:
        sol = [var.get_assigned_value() for row in var_array for var in row]
        details = ("Expected an unsolvable board but got a complete assignment: %s" % sol)
        return 0, details, 1

def check_futoshiki_solution(board, var_array):
    """
    Given the original board (a list-of-lists where each row has 2*n - 1 entries)
    and the 2D list of Variables (n x n), check that:
      - Every cell is assigned a nonzero value.
      - Each row and each column contains distinct values.
      - All horizontal inequality constraints are satisfied.
    Returns a tuple (True, "") if valid, else (False, error_message).
    """
    n = len(board)
    # Build solution matrix from var_array (each row corresponds to the n cell assignments)
    sol = []
    for row in var_array:
        sol_row = [var.get_assigned_value() for var in row]
        sol.append(sol_row)
    # Check all cells are assigned and nonzero
    for i in range(n):
        for j in range(n):
            if sol[i][j] is None or sol[i][j] == 0:
                return False, f"Cell ({i},{j}) is unassigned or zero."
    # Check row uniqueness
    for i in range(n):
        if len(set(sol[i])) != n:
            return False, f"Row {i} does not have distinct values: {sol[i]}"
    # Check column uniqueness
    for j in range(n):
        col = [sol[i][j] for i in range(n)]
        if len(set(col)) != n:
            return False, f"Column {j} does not have distinct values: {col}"
    # Check inequality constraints in each row
    for i in range(n):
        # Each row in board has 2*n - 1 elements (numbers at even indices, inequalities at odd indices)
        for j in range(n - 1):
            inequality = board[i][2*j + 1]
            if inequality == '.':
                continue
            left = sol[i][j]
            right = sol[i][j+1]
            if inequality == '<' and not (left < right):
                return False, f"Inequality violation in row {i} between columns {j} and {j+1}: {left} < {right} is false."
            if inequality == '>' and not (left > right):
                return False, f"Inequality violation in row {i} between columns {j} and {j+1}: {left} > {right} is false."
    return True, ""

def futoshiki_model1_validity_test(propagator, name="futoshiki_model1_validity_test"):
    """
    Run futoshiki_csp_model_1 on a 3x3 board and then check that the resulting assignment
    is a valid Futoshiki solution (all cells assigned, distinct in rows/columns, and inequalities hold).
    Board (3x3):
      [0, '<', 0, '.', 0]
      [0, '.', 0, '>', 0]
      [0, '.', 0, '<', 0]
    """
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    board = [
        [0, '<', 0, '.', 0],
        [0, '.', 0, '>', 0],
        [0, '.', 0, '<', 0]
    ]
    result = student_models.futoshiki_csp_model_1(board)
    if result is None:
        return 0, "futoshiki_csp_model_1 returned None", 1
    csp, var_array = result

    bt_solver = cspbase.BT(csp)
    set_timeout(TIMEOUT)
    bt_solver.bt_search(propagator)
    reset_timeout()

    valid, msg = check_futoshiki_solution(board, var_array)
    if valid:
        return 1, "", 1
    else:
        return 0, f"Solution validity check failed: {msg}", 1


def test_futoshiki_model1_simple(propagator, name="futoshiki_model1_simple"):
    """
    Test simple solvable 2x2 puzzle.
    Board (2x2):
      [0, '<', 0]
      [0, '.', 2]
    Expected solution: [1, 2, 2, 1]
    """
    board = [
        [0, '<', 0],
        [0, '.', 2]
    ]
    expected_solution = [1, 2, 2, 1]
    
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    csp, var_array = student_models.futoshiki_csp_model_1(board)
    solver = cspbase.BT(csp)
    solver.bt_search(propagator)

    solution = [var.get_assigned_value() for row in var_array for var in row]
    if solution == expected_solution:
        return 1, "", 1
    else:
        details = f"Expected solution {expected_solution}, but got {solution}"
        return 0, details, 1


def test_futoshiki_model1_with_prefilled_cells(propagator, name="futoshiki_model1_preassigned"):
    """
    Test puzzle with preassigned cells (3x3).
    Board:
      [1, '.', 0, '.', 0]
      [0, '>', 0, '.', 0]
      [0, '.', 0, '<', 3]
    Expected to produce a valid solution without conflicts.
    """
    board = [
        [1, '.', 0, '.', 0],
        [0, '>', 0, '.', 0],
        [0, '.', 0, '<', 3]
    ]
    
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    csp, var_array = student_models.futoshiki_csp_model_1(board)
    solver = cspbase.BT(csp)
    solver.bt_search(propagator)

    valid, msg = check_futoshiki_solution(board, var_array)
    if valid:
        return 1, "", 1
    else:
        details = f"Solution validity check failed: {msg}"
        return 0, details, 1


def test_futoshiki_model1_unsolvable(propagator, name="futoshiki_model1_unsolvable"):
    """
    Test unsolvable puzzle due to conflicting inequalities.
    Board (2x2):
      [1, '>', 2]
      [0, '.', 0]
    Expected: no solution (unsolvable scenario).
    """
    board = [
        [1, '>', 2],
        [0, '.', 0]
    ]
    
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    csp, var_array = student_models.futoshiki_csp_model_1(board)
    solver = cspbase.BT(csp)
    result = solver.bt_search(propagator)

    if result is None:
        return 1, "", 1
    else:
        details = "Expected no solution, but found one."
        return 0, details, 1


def test_futoshiki_model1_edge_case_empty_board(propagator, name="futoshiki_model1_empty_board"):
    """
    Test edge case of an entirely empty 2x2 board.
    No inequalities or pre-filled values.
    Should find at least one valid solution.
    """
    board = [
        [0, '.', 0],
        [0, '.', 0]
    ]
    
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    csp, var_array = student_models.futoshiki_csp_model_1(board)
    solver = cspbase.BT(csp)
    solver.bt_search(propagator)

    solution = [var.get_assigned_value() for row in var_array for var in row]
    if None not in solution and len(solution) == 4 and len(set(solution[:2])) == 2 and len(set(solution[:2])) == len(set(solution[2:])):
        return 1, "", 1
    else:
        details = "No valid solution found or solution invalid."
        return 0, details, 1

def futoshiki_model2_solvable_test(propagator, name="futoshiki_model2_solvable_test"):
    """
    Test futoshiki_csp_model_2 (if implemented) on a solvable board.
    Uses the same board as futoshiki_model1_solvable_test.
    Expected solution (row-major): [1, 2, 3, 3, 1, 2, 2, 3, 1]
    """
    try:
        import futoshiki_csp as student_models
    except ImportError:
        return 0, "futoshiki_csp module not found", 1

    if not hasattr(student_models, "futoshiki_csp_model_2"):
        return 0, "futoshiki_csp_model_2 not implemented", 1

    board = [
        [1, '<', 0, '.', 0],
        [0, '.', 0, '.', 2],
        [2, '.', 0, '>', 0]
    ]
    expected_solution = [1, 2, 3, 3, 1, 2, 2, 3, 1]
    result = student_models.futoshiki_csp_model_2(board)
    if result is None:
        return 0, "futoshiki_csp_model_2 returned None", 1
    csp, var_array = result

    bt_solver = cspbase.BT(csp)
    set_timeout(TIMEOUT)
    bt_solver.bt_search(propagator)
    reset_timeout()

    sol = [var.get_assigned_value() for row in var_array for var in row]
    if sol == expected_solution:
        return 1, "", 1
    else:
        return 0, f"Expected solution {expected_solution}, but got {sol}", 1






#######################################
# MAIN FUNCTION
#######################################
def main():
    parser = argparse.ArgumentParser(description="Run CSP Futoshiki autograder.")
    parser.add_argument("--verbose", action="store_true", help="Enable verbose output")
    parser.add_argument("--test", "-t", nargs="+",
                        help="Specify one or more test names to run (e.g. test_simple_fc test_tiny_adder_fc). "
                             "If omitted, all tests will be run.")
    args = parser.parse_args()
    verbose = args.verbose

    print("Running Futoshiki/Propagators Autograder...\n")

    # Import student modules (fallback to solution modules if needed)
    try:
        import propagators as student_propagators
    except ImportError:
        print("Could not import student's propagators. Using solution_propagators as fallback.\n")
        student_propagators = soln_propagators

    try:
        import futoshiki_csp as student_models
    except ImportError:
        student_models = None
        
    # Helper function: run an individual test.
    # If verbose is not set, redirect output (stdout) to an in-memory buffer.
    def run_test(test_func, *test_args, test_name=""):
        try:
            with contextlib.redirect_stdout(io.StringIO()) if not verbose else contextlib.nullcontext():
                set_timeout(TIMEOUT)  # 10s timeout per test
                s, detail, ms = test_func(*test_args)
                reset_timeout()
            return s, detail, ms
        except TimeoutException:
            return 0, f"{test_name} - TIMEOUT", 1
        except Exception:
            tb = traceback.format_exc()
            return 0, f"{test_name} - RUNTIME ERROR:\n{tb}", 1

    # List of tests including an extra field for the test group
    tests = [
        (example_csp_test, student_propagators.prop_BT, "example_csp_test"),
        (test_prop_FC, soln_propagators.prop_FC, "test_prop_FC"),
        (jha_test_prop_FC, student_propagators, "jha_test_prop_FC"),
        (test_prop_FC_no_pruning, soln_propagators.prop_FC, "test_prop_FC_no_prune"),
        (test_prop_FC_DWO, soln_propagators.prop_FC, "test_prop_FC_DWO"),
        (jha_test_prop_GAC, student_propagators, "jha_test_prop_GAC"),
        (test_GAC_simple, student_propagators.prop_GAC, "test_GAC_simple"),
        (test_GAC_prune, student_propagators.prop_GAC, "test_GAC_prune"),
        (test_GAC_domain_wipeout, student_propagators.prop_GAC, "test_GAC_domain_wipeout"),
        (test_GAC_chain_reaction, student_propagators.prop_GAC, "test_GAC_chain_reaction"),
        (jha_test_ord_mrv, None, "jha_test_ord_mrv"),
        (test_ord_mrv_simple, student_propagators, "test_ord_mrv_simple"),
        (test_ord_mrv_all_assigned, student_propagators, "test_ord_mrv_all_assigned"),
        (test_ord_mrv_tie_break, student_propagators, "test_ord_mrv_tie_break"),
        (test_ord_mrv_empty_csp, student_propagators, "test_ord_mrv_empty_csp"),
        (jha_futoshiki_model1_solvable_test, student_propagators.prop_BT, "jha_futoshiki_model1_solvable_test"),
        (futoshiki_model1_unsolvable_test, student_propagators.prop_BT, "futoshiki_model1_unsolvable_test"),
        (futoshiki_model1_validity_test, student_propagators.prop_BT, "futoshiki_model1_validity_test"),
        (test_futoshiki_model1_simple, student_propagators.prop_BT, "test_futoshiki_model1_simple"),
        (test_futoshiki_model1_with_prefilled_cells, student_propagators.prop_BT, "test_futoshiki_model1_with_prefilled_cells"),
        (test_futoshiki_model1_unsolvable, student_propagators.prop_BT, "futoshiki_model1_validity_test"),
        (test_futoshiki_model1_edge_case_empty_board, student_propagators.prop_BT, "test_futoshiki_model1_edge_case_empty_board"),
        (futoshiki_model2_solvable_test, student_propagators.prop_BT, "futoshiki_model2_solvable_test"),
        
        (example_csp_test, student_propagators.prop_BT, "example_csp_test"),
        (futoshiki_model1_solvable_test, student_propagators.prop_BT, "futoshiki_model1_solvable_test"),
        (futoshiki_model1_unsolvable_test, student_propagators.prop_BT, "futoshiki_model1_unsolvable_test"),
        (futoshiki_model1_validity_test, student_propagators.prop_BT, "futoshiki_model1_validity_test"),
        (futoshiki_model2_solvable_test, student_propagators.prop_BT, "futoshiki_model2_solvable_test"),
        (futoshiki_model2_unsolvable_test, student_propagators.prop_BT, "futoshiki_model2_unsolvable_test"),
        (solved_board_test, student_propagators.prop_BT, "solved_board_test"),
        (ord_mrv_test, None, "ord_mrv_test"),
        (prop_FC_test, student_propagators, "prop_FC_test"),
        (prop_GAC_test, student_propagators, "prop_GAC_test"),
        (inequality_propagation_test, student_propagators, "inequality_propagation_test"),
        (inequality_propagation_reverse_test, student_propagators, "inequality_propagation_reverse_test"),
        (all_diff_test, student_propagators, "all_diff_test"),
        (preassigned_domain_test, student_propagators.prop_BT, "preassigned_domain_test"),
        (all_blank_board_test, student_propagators.prop_BT, "all_blank_board_test"),
        (duplicate_preassignment_test, student_propagators.prop_BT, "duplicate_preassignment_test"),
        (preassignment_consistency_test, student_propagators.prop_BT, "preassignment_consistency_test"),
        (solved_board_model2_test, student_propagators.prop_BT, "solved_board_model2_test"),
        (prop_FC_extended_chain_test, student_propagators, "prop_FC_extended_chain_test"),
        (prop_GAC_extended_chain_test, student_propagators, "prop_GAC_extended_chain_test"),
        (inequality_propagation_multiple_test, student_propagators, "inequality_propagation_multiple_test"),
        (all_diff_large_test, student_propagators, "all_diff_large_test"),
        (futoshiki_4x4_solvable_test, student_propagators.prop_BT, "futoshiki_4x4_solvable_test"),
        (futoshiki_4x4_unsolvable_test, student_propagators.prop_BT, "futoshiki_4x4_unsolvable_test"),
        (solved_board_4x4_test, student_propagators.prop_BT, "solved_board_4x4_test"),
        (duplicate_preassignment_test_4x4, student_propagators.prop_BT, "duplicate_preassignment_test_4x4"),
        (preassigned_domain_test_4x4, student_propagators.prop_BT, "preassigned_domain_test_4x4"),
        (all_blank_board_test_4x4, student_propagators.prop_BT, "all_blank_board_test_4x4"),
        (ord_mrv_all_equal_test, None, "ord_mrv_all_equal_test"),
        (prop_FC_inconsistency_test, student_propagators, "prop_FC_inconsistency_test"),
        (prop_GAC_inconsistency_test, student_propagators, "prop_GAC_inconsistency_test"),
        (example_csp_invalid_test, student_propagators.prop_BT, "example_csp_invalid_test"),
        (all_diff_test_extended, student_propagators, "all_diff_test_extended"),
        (complex_csp_test, student_propagators.prop_BT, "complex_csp_test"),
        (futoshiki_model1_random_test, student_propagators.prop_BT, "futoshiki_model1_random_test"),
        (futoshiki_model2_4x4_solvable_test, student_propagators.prop_BT, "futoshiki_model2_4x4_solvable_test"),
        (futoshiki_model2_4x4_unsolvable_test, student_propagators.prop_BT, "futoshiki_model2_4x4_unsolvable_test"),
        (preassignment_consistency_test_4x4, student_propagators.prop_BT, "preassignment_consistency_test_4x4"),
        (solved_board_model2_4x4_test, student_propagators.prop_BT, "solved_board_model2_4x4_test"),
        (prop_FC_complex_test, student_propagators, "prop_FC_complex_test"),
        (prop_GAC_complex_test, student_propagators, "prop_GAC_complex_test"),
        (ord_mrv_tiebreak_extended_test, None, "ord_mrv_tiebreak_extended_test"),
        (inequality_propagation_chain_test, student_propagators, "inequality_propagation_chain_test"),
        (example_csp_multiple_constraints_test, student_propagators.prop_BT, "example_csp_multiple_constraints_test"),
        (future_extra_test, student_propagators.prop_BT, "future_extra_test")
        # Add more tests here
        # there are 6 test groups
    ]

    # If the user provided specific test names, filter out tests not matching those names.
    if args.test:
        specified = set(args.test)
        tests = [t for t in tests if t[2] in specified]
        if not tests:
            print("No matching tests found for the provided names. Exiting.")
            return

    # Initialize dictionaries to track scores per group.
    overall_score = 0
    overall_max = 0

    # Run each test, and print a formatted result.
    for test_func, test_arg, test_name in tests:
        s, detail, ms = run_test(test_func, test_arg, test_name=test_name)
        overall_score += s
        overall_max += ms

        # Determine status tag based on score
        if s == ms:
            status = "[PASSED]"
        elif s > 0:
            status = "[PARTIAL]"
        else:
            status = "[FAIL]"

        # If no details, print "None"
        detail_to_print = detail.strip() if detail.strip() else "None"

        # Print the test result in the desired format.
        print(f"{status} {test_name} => score: {s}/{ms} details: {detail_to_print}")

    print("Overall Test Score: %d/%d" % (overall_score, overall_max))


if __name__ == "__main__":
    main()
