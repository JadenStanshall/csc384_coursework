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
        # Add more tests here
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
