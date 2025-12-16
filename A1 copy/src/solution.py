#   Look for #IMPLEMENT tags in this file. These tags indicate what has
#   to be implemented to complete the warehouse domain.

#   You may add only standard python imports
#   You may not remove any imports.
#   You may not import or otherwise source any of your own files

# my alternate heuristic is the weighted sum of the following values:
# 1. sum of manhattan distances from each robot to nearest box
# 2. sum of manhattan distances from each box to closest storage space
# 3. a clutter factor which quantifies how crowded the boxes are
#       the clutter factor is the average number of adjacent objects to each box

import os  # for time functions
import math  # for infinity
from search import *  # for search engines
from sokoban import sokoban_goal_state, SokobanState, Direction, PROBLEMS  # for Sokoban specific classes and problems
DEV_MODE = False

# SOKOBAN HEURISTICS
def manhattan_distance(start, end): # calculate manhattan distance between two points
    return abs(start[0] - end[0]) + abs(start[1] - end[1])

def box_on_storage(box, all_storage): # check if a box is on a storage space
    return box in all_storage

def game_limits(state): # contruct the boarders of the game as a set of obstacles
    limits = set()
    for i in range(-1, state.width + 1):
        limits.add((i, -1))
        limits.add((i, state.height))
    for i in range(0, state.height):
        limits.add((-1, i))
        limits.add((state.width, i))
    return limits

def corner_stuck(box, all_obstacles): # check if a box is stuck in a corner
    x = box[0]
    y = box[1]
    walls = [(x, y+1),
             (x, y-1),
             (x+1, y),
             (x-1, y),
             (x, y+1)] # initialize potential wall locations which would lead to a stuck box
             # note: the first element is repeated to make the loop easier
    for i in range(0, len(walls)):
        if walls[i] in all_obstacles and walls[i+1] in all_obstacles: # if two or more adjacent edges of the box are touching walls/obstacles, the box is stuck
            return True
        else:
            return False

def num_adj(box, all_objects): # quantify how crowded a box is
    x = box[0]
    y = box[1]
    adj = 0
    if (x+1, y) in all_objects:
        adj += 1
    if (x-1, y) in all_objects:
        adj += 1
    if (x, y+1) in all_objects:
        adj += 1
    if (x, y-1) in all_objects:
        adj += 1
    return adj

def unplaced_boxes(state): #  return set of boxes that are not on storage spaces
    placed_boxes = state.boxes.intersection(state.storage)
    unplaced_boxes = state.boxes - placed_boxes
    return unplaced_boxes


def heur_alternate(state): # PART 2: NON TRIVIAL HEURISTIC: consider issues that the manhattan heuristic ignores (many boxes assigned to same storage space, etc.)
    # IMPLEMENT
    '''a better heuristic'''
    '''INPUT: a sokoban state'''
    '''OUTPUT: a numeric value that serves as an estimate of the distance of the state to the goal.'''
    # heur_manhattan_distance has flaws.
    # Write a heuristic function that improves upon heur_manhattan_distance to estimate distance between the current state and the goal.
    # Your function should return a numeric value for the estimate of the distance to the goal.
    # EXPLAIN YOUR HEURISTIC IN THE COMMENTS. Please leave this function (and your explanation) at the top of your solution file, to facilitate marking.

    # if a box is in a situation where it is impossible for it to reach a storage space, make heiristic infinite
    # this includes cases where a box is stuck in a corner with walls on at least 2 adjacent sides and is not already on a storage space
    # note: a box stuck in a corner can be considered as a wall when detecting subsequent impossble scenarios
    # this means the robot should not be tempted to move a box such that it makes another box get stuck
    # however, we do not necessarily need to account for that case as getting a box stuck in the first place
    # already results in an impossible scenario and is assigned an infinite heuristic value regardless

    # also add manhattan distance from robot to nearest box and then again from each box to closest storage space
    # this incentivizes the robot to move towards a box if it is not already adjacent to one

    # if a box is on a storage space, it does not necessarily mean it should not be moved, a the optimal solution may require it to be moved

    all_obstacles = state.obstacles.union(game_limits(state)) # all obstacles include walls and obstacles
    all_storage = state.storage # all storage spaces
    all_objects = all_obstacles.union(state.boxes).union(state.robots) # all objects on the board
    for i in state.boxes: # for every box
        if corner_stuck(i, all_obstacles) and not box_on_storage(i, all_storage): # if box is stuck in a corner and not on a storage space
            return math.inf # exit immediately and begin computing heuristic for the next successor state, save time
    
    lowest_manhattan_distances_robots_to_boxes = []
    for i in range(0, len(state.robots)): # prepared to handle case of multiple robots
        lowest_manhattan_distances_robots_to_boxes.append((manhattan_distance((0, 0), (state.width, state.height)))) # initialize with max value
        for j in state.boxes: # for every box that is not on a storage space
            cur_manhattan_distance_robot_to_box = manhattan_distance(state.robots[i], j)
            if cur_manhattan_distance_robot_to_box < lowest_manhattan_distances_robots_to_boxes[i]:
                lowest_manhattan_distances_robots_to_boxes[i] = cur_manhattan_distance_robot_to_box
    sum_robot_to_box = sum(lowest_manhattan_distances_robots_to_boxes) # sum of manhattan distances from each robot to their nearest box

    # looking at neighbouring squares to each box
    clutter_factor = 0 # if a box is surrounded by other objects, it is harder to move
    for i in state.boxes:
        clutter_factor += num_adj(i, all_objects)

    clutter_factor = clutter_factor / len(state.boxes) # average number of adjacent objects to each box


    return sum_robot_to_box + heur_manhattan_distance(state) + 0.55 * clutter_factor



def heur_zero(state):
    '''Zero Heuristic can be used to make A* search perform uniform cost search'''
    return 0

def heur_manhattan_distance(state): # PART 1: MANHATTAN DISTANCE between each box and the closest storage space, sum across all boxes
    # IMPLEMENT
    '''admissible sokoban puzzle heuristic: manhattan distance'''
    '''INPUT: a sokoban state'''
    '''OUTPUT: a numeric value that serves as an estimate of the distance of the state to the goal.'''
    # We want an admissible heuristic, which is an optimistic heuristic.
    # It must never overestimate the cost to get from the current state to the goal.
    # The sum of the Manhattan distances between each box that has yet to be stored and the storage point nearest to it is such a heuristic.
    # When calculating distances, assume there are no obstacles on the grid.
    # You should implement this heuristic function exactly, even if it is tempting to improve it.
    # Your function should return a numeric value; this is the estimate of the distance to the goal.
    if DEV_MODE:
        print("Width: ", state.width)
        print("Height: ", state.height)
        print("Boxes: ", state.boxes)
        print("Storage: ", state.storage)
        print("Robots: ", state.robots)
        print("Obstacles: ", state.obstacles)
        print("\n")

    sum_manhattan_distance = 0
    for i in state.boxes:
        lowest_manhattan_distance = manhattan_distance((0, 0), (state.width, state.height))
        for j in state.storage:
            cur_manhattan_distance = manhattan_distance(i, j)
            if cur_manhattan_distance < lowest_manhattan_distance:
                lowest_manhattan_distance = cur_manhattan_distance
        sum_manhattan_distance += lowest_manhattan_distance

    return sum_manhattan_distance  # CHANGE THIS

if DEV_MODE:
    state1 = SokobanState("START", 0, None, 6, 6,  # dimensions
                 ((0, 0), (0, 2), (0, 4)),  # robots
                 frozenset(((1, 0), (1, 2), (1, 4))),  # boxes
                 frozenset(((5, 0), (5, 2), (0, 5))),  # storage
                 frozenset()  # obstacles
                 )
    
    state2 = SokobanState("START", 0, None, 4, 7,  # dimensions
                 ((0, 3),),  # robots
                 frozenset(((1, 2), (1, 3), (1, 4))),  # boxes
                 frozenset(((2, 1), (2, 5), (1, 3))),  # storage
                 frozenset(((1, 1), (1, 5)))  # obstacles
                 )
    
    print(heur_manhattan_distance(state2))
    state2.print_state()
    print(game_limits(state2))


def fval_function(sN, weight): # PART 3: look for goal value and heursitic value and come up with an f val function (weighted sum)
    # given each node and the weight of each node (straightforward)
    # IMPLEMENT
    """
    Provide a custom formula for f-value computation for Anytime Weighted A star.
    Returns the fval of the state contained in the sNode.

    @param sNode sN: A search node (containing a SokobanState)
    @param float weight: Weight given by Anytime Weighted A star
    @rtype: float
    """
    return sN.gval + weight * sN.hval

# SEARCH ALGORITHMS (implement (ez))
def weighted_astar(initial_state, heur_fn, weight, timebound): # find solution to each problem wtih weighted A*
    # IMPLEMENT    
    '''Provides an implementation of weighted a-star, as described in the HW1 handout'''
    '''INPUT: a sokoban state that represents the start state and a timebound (number of seconds)'''
    '''OUTPUT: A goal state (if a goal is found), else False as well as a SearchStats object'''
    '''implementation of weighted astar algorithm'''

    wrapped_fval_function = (lambda sN: fval_function(sN, weight))
    search_engine = SearchEngine('custom', 'full')
    search_engine.init_search(initial_state, sokoban_goal_state, heur_fn, wrapped_fval_function)
    soln, stats = search_engine.search(timebound)

    return soln, stats  # CHANGE THIS


def iterative_astar(initial_state, heur_fn, weight=1, timebound=5):  # uses f(n), see how autograder initializes a search line 88
    # IMPLEMENT
    '''Provides an implementation of realtime a-star, as described in the HW1 handout'''
    '''INPUT: a sokoban state that represents the start state and a timebound (number of seconds)'''
    '''OUTPUT: A goal state (if a goal is found), else False as well as a SearchStats object'''
    '''implementation of iterative astar algorithm'''

    start = os.times()[0]
    end = start + timebound

    wrapped_fval_function = (lambda sN: fval_function(sN, weight))
    search_engine = SearchEngine('custom', 'full')
    search_engine.init_search(initial_state, sokoban_goal_state, heur_fn, wrapped_fval_function)
    weight_reduction_factor = 0.5 # reduce weight by 0.1 each iteration

    costbound = [math.inf, math.inf, math.inf] # initialize with max values, no bound on cost for first iteration
                 # g_val,    h_val,    f_val
    timebound = end - os.times()[0]

    best_soln, best_stats = search_engine.search(timebound, costbound) # search for solution
    if best_soln == False:
        return best_soln, best_stats # return false if no solution found
    else:
        count = 1 # success, we have a solution
        while timebound > 0.05: # while we still have time
            best_soln_hval = heur_fn(best_soln) # update heuristic value of current solution
            costbound = [best_soln.gval, best_soln_hval, best_soln.gval + best_soln_hval] # update lowest costbound
            weight = 1 + ((weight-1) * weight_reduction_factor) # update weight
            timebound = end - os.times()[0] # new time bound
            new_soln, new_stats = search_engine.search(timebound, costbound) # search again with new timebound and weight
            if new_soln == False:
                return best_soln, best_stats
            timebound = end - os.times()[0] # update timebound
            new_soln_hval = heur_fn(new_soln) # update heuristic value of new solution
            if new_soln.gval + weight * new_soln_hval < costbound[2]: # if new solution is better than the current best solution
                best_soln = new_soln # update best solution

        return best_soln, best_stats # return best solution if time runs out


def iterative_gbfs(initial_state, heur_fn, timebound=5):  # only use h(n)
    # IMPLEMENT
    '''Provides an implementation of anytime greedy best-first search, as described in the HW1 handout'''
    '''INPUT: a sokoban state that represents the start state and a timebound (number of seconds)'''
    '''OUTPUT: A goal state (if a goal is found), else False'''
    '''implementation of iterative gbfs algorithm'''

    start = os.times()[0]
    end = start + timebound

    search_engine = SearchEngine('best_first', 'full')
    search_engine.init_search(initial_state, sokoban_goal_state, heur_fn)

    costbound = [math.inf, math.inf, math.inf] # initialize with max values, no bound on cost for first iteration
                 # g_val,    h_val,    f_val
    timebound = end - os.times()[0]

    best_soln, best_stats = search_engine.search(timebound, costbound) # search for solution
    if best_soln == False:
        return best_soln, best_stats # return false if no solution found
    else:
        costbound = [best_soln.gval, math.inf,math.inf] # update lowest costbound, only care abt g_val
        timebound = end - os.times()[0]
        while timebound > 0.05: # while we still have time
            new_soln, new_stats = search_engine.search(timebound, costbound)
            if new_soln == False:
                return best_soln, best_stats # return previous best solution if no new solution found
            if new_soln.gval <= costbound[0]: # if new solution is better than the current best solution
                costbound = [new_soln.gval, math.inf, math.inf] # update lowest costbound, only care abt g_val
                best_soln = new_soln # update best solution
            timebound = end - os.times()[0]
        return best_soln, best_stats # return best solution if time runs out