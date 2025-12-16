# Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = futoshiki_csp_model_1(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the Futoshiki puzzle.

1. futoshiki_csp_model_1 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only
      binary not-equal constraints for both the row and column constraints.

2. futoshiki_csp_model_2 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only n-ary
      all-different constraints for both the row and column constraints.
    
    The input board is specified as a list of n lists. Each of the n lists
    represents a row of the board. If a 0 is in the list it represents an empty
    cell. Otherwise if a number between 1--n is in the list then this
    represents a pre-set board position.

    Each list is of length 2n-1, with each space on the board being separated
    by the potential inequality constraints. '>' denotes that the previous
    space must be bigger than the next space; '<' denotes that the previous
    space must be smaller than the next; '.' denotes that there is no
    inequality constraint.

    E.g., the board

    -------
    | > |2|
    | | | |
    | | < |
    -------
    would be represented by the list of lists

    [[0,>,0,.,2],
     [0,.,0,.,0],
     [0,.,0,<,0]]

'''
import cspbase
import itertools

def create_all_diff_constraints(name, variables):
    constraint = cspbase.Constraint(f"C({name})", variables)
    domains = []
    for var in variables:
        domains.append(var.cur_domain())

    all_combinations = itertools.product(*domains)

    all_diff_tuples = []
    for combination in all_combinations:
        if len(set(combination)) == len(combination):  # all items unique
            all_diff_tuples.append(combination)

    constraint.add_satisfying_tuples(all_diff_tuples)
    return [constraint]

def satisfies_inequality(v1, v2, operator):
    if operator == '>':
        return v1 > v2
    elif operator == '<':
        return v1 < v2
    return False

def create_inequality_constraint(name1, name2, var1, var2, operator):
    constraint_name = f"C({name1},{name2})"

    constraint = cspbase.Constraint(constraint_name, [var1, var2])

    dom1 = var1.cur_domain()
    dom2 = var2.cur_domain()

    satisfying_tuples = []
    
    for x, y in itertools.product(dom1, dom2): # all combinations
        if satisfies_inequality(x, y, operator):
            satisfying_tuples.append((x, y))

    constraint.add_satisfying_tuples(satisfying_tuples)
    return [constraint]

def add_inequality_constraint(var1, var2, operator, constraint_name, futoshiki_csp):
    valid_tuples = []
    if operator == '<':
        for x in var1.domain():
            for y in var2.domain():
                if x < y:
                    valid_tuples.append((x, y))
    elif operator == '>':
        for x in var1.domain():
            for y in var2.domain():
                if x > y:
                    valid_tuples.append((x, y))
    constraint = cspbase.Constraint(constraint_name, [var1, var2])
    constraint.add_satisfying_tuples(valid_tuples)
    futoshiki_csp.add_constraint(constraint)

def futoshiki_csp_model_1(futo_grid):
    '''
    csp with only binary constraints
    '''

    size = len(futo_grid)
    variables = []
    var_grid = []

    # init everything
    for row_idx in range(len(futo_grid)):
        var_row = []
        row = futo_grid[row_idx]
        for col_idx in range(len(row)):
            cell = row[col_idx]
            if isinstance(cell, int):
                if cell != 0:
                    domain = [cell]
                else:
                    domain = list(range(1, size + 1))
                var = cspbase.Variable(f"V_{row_idx}_{col_idx}", domain)
                var_row.append(var)
                variables.append(var)
        var_grid.append(var_row)
        
    futoshiki_csp = cspbase.CSP("Futoshiki_Binary_Only", variables)

    # inequality constraints
    for idx in range(size):
        for i in range(size):
            for j in range(i + 1, size):
                # rows
                row_constraint = cspbase.Constraint(f"RowNE_{idx}_{i}_{j}", [var_grid[idx][i], var_grid[idx][j]])
                row_constraint.add_satisfying_tuples([(x, y) for x in var_grid[idx][i].domain() for y in var_grid[idx][j].domain() if x != y])
                futoshiki_csp.add_constraint(row_constraint)

                # cols
                col_constraint = cspbase.Constraint(f"ColNE_{idx}_{i}_{j}", [var_grid[i][idx], var_grid[j][idx]])
                col_constraint.add_satisfying_tuples([(x, y) for x in var_grid[i][idx].domain() for y in var_grid[j][idx].domain() if x != y])
                futoshiki_csp.add_constraint(col_constraint)

    for row in range(size):
        for col in range(len(futo_grid[row])):
            cell = futo_grid[row][col]
            if cell in ('<', '>'):
                if col % 2 == 1:  # horizontal
                    left_var = var_grid[row][col // 2]
                    right_var = var_grid[row][(col // 2) + 1]
                    add_inequality_constraint(left_var, right_var, cell, f"HorIneq_{row}_{col}", futoshiki_csp)
                else:  # vertical
                    top_var = var_grid[row][col // 2]
                    bottom_var = var_grid[row + 1][col // 2]
                    add_inequality_constraint(top_var, bottom_var, cell, f"VerIneq_{row}_{col}", futoshiki_csp)

    return futoshiki_csp, var_grid



def futoshiki_csp_model_2(futo_grid):
    '''
    csp with mixed cnstraints
    '''
    size = len(futo_grid)
    variables = []
    constraints = []
    domain = list(range(1, size + 1))
    inequality_symbols = ['.', '>', '<']
    
    variable_grid = []
    inequality_grid = []
    
    # separate variables and inequalities
    for i in range(len(futo_grid)):
        variables_row = []
        inequalities_row = []
    
        row = futo_grid[i]
        for j in range(len(row)):
            value = row[j]
            if value not in inequality_symbols:
                var_name = f"V{i}{j//2}"
                if value != 0:
                    var_domain = [value]
                else:
                    var_domain = domain

                variable = cspbase.Variable(var_name, var_domain)
                if value != 0:
                    variable.assign(value)
                variables_row.append(variable)
                variables.append(variable)
            else:
                inequalities_row.append(value)
    
        variable_grid.append(variables_row)
        inequality_grid.append(inequalities_row)
    
    # constraints
    for i in range(size):
        row_variables = variable_grid[i]
        column_variables = [variable_grid[j][i] for j in range(size)]
        
        # row and col
        constraints += create_all_diff_constraints(f"Row{i}", row_variables)
        constraints += create_all_diff_constraints(f"Col{i}", column_variables)
        
        # inequality
        for j in range(size - 1):
            if inequality_grid[i][j] != '.':
                constraints += create_inequality_constraint(f"V{i}{j}", f"V{i}{j+1}", row_variables[j], row_variables[j+1], inequality_grid[i][j])

    csp = cspbase.CSP(f"Futoshiki Size {size} Model 2", variables)
    for constraint in constraints:
        csp.add_constraint(constraint)
    
    return csp, variable_grid
