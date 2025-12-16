# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
		 
		 
var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable 

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''


def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''
    forward checking propagation on csp, with newVar (if any) assigned.
    '''

    pruned_values = []

    if newVar:
        constraints = csp.get_cons_with_var(newVar)
    else:
        constraints = csp.get_all_cons()

    for constraint in constraints:
        unassigned_vars = []
        for var in constraint.get_scope():
            if not var.is_assigned():
                unassigned_vars.append(var)
        
        # check if only one unassigned variable left
        if len(unassigned_vars) == 1:
            unassigned_var = unassigned_vars[0]
            # make copy to avoid modifying the original domain
            for val in unassigned_var.cur_domain()[:]:
                if not constraint.has_support(unassigned_var, val):
                    unassigned_var.prune_value(val)
                    if unassigned_var.cur_domain_size() == 0:
                        return False, [(unassigned_var, val)]
                    else:
                        pruned_values = [(unassigned_var, val)]
                        return True, pruned_values
                        
    return True, []


def prop_GAC(csp, newVar=None):
    '''
    GAC propagation on csp, with newVar (if any) assigned
    '''
    pruned_values = []

    if newVar:
        gac_queue = csp.get_cons_with_var(newVar)
    else:
        gac_queue = csp.get_all_cons()

    while gac_queue:
        constraint = gac_queue.pop(0)

        for var in constraint.get_scope():
            for val in var.cur_domain()[:]:
                if not constraint.has_support(var, val):
                    var.prune_value(val)
                    pruned_values.append((var, val))

                    if var.cur_domain_size() == 0:
                        return False, pruned_values

                    for related_constraint in csp.get_cons_with_var(var):
                        if related_constraint not in gac_queue and related_constraint != constraint:
                            gac_queue.append(related_constraint)

    return True, pruned_values



def ord_mrv(csp):
    '''
    minimum remaining values variable ordering heuristic
    '''

    unassigned_vars = []
    for var in csp.get_all_vars():
        if not var.is_assigned():
            unassigned_vars.append(var)


    if not unassigned_vars:
        return None

    min_var = unassigned_vars[0]

    for var in unassigned_vars[1:]:
        if var.cur_domain_size() < min_var.cur_domain_size():
            min_var = var

    return min_var
