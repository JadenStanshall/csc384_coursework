"""
An AI player for Othello. 
"""

import random
import sys
import time

# You can use the functions from othello_shared to write your AI
from othello_shared import find_lines, get_possible_moves, get_score, play_move

# maps board states to minimax values
cache = {} # Use this for state caching

def eprint(*args, **kwargs): #use this for debugging, to print to sterr
    print(*args, file=sys.stderr, **kwargs)

def get_successor_utility(board, color, col, row):
    successor_board = play_move(board, color, col, row)
    return compute_utility(successor_board, color)

def node_ordering_heur(board, moves, color, current_player):
    move_utility = {}
    sorted_moves = []
    for move in moves:
        (col, row) = move
        successor_utility = get_successor_utility(board, color, col, row)
        move_utility[move] = successor_utility
    
    sorted_move_utility = dict(sorted(move_utility.items(), key=lambda item: item[1], reverse=True))
    
    for move in sorted_move_utility:
        sorted_moves.append(move)
    return sorted_moves

def compute_utility_1(board, color):
    # IMPLEMENT!
    """
    Method to compute the utility value of board.
    INPUT: a game state and the player that is in control
    OUTPUT: an integer that represents utility
    """
    
    score = get_score(board) # (dark, light)
    
    if color == 1: # dark
        return score[0] - score[1]
    if color == 2: # light
        return score[1] - score[0]
    else:
        raise RuntimeError("colour must be 1 or 2")

def compute_utility(board, color):
    
    # set opp AND find raw utility
    if color == 1:
        opp = 2
        utility = get_score(board)[0] - get_score(board)[1]
    else:
        opp = 1
        utility = get_score(board)[1] - get_score(board)[0]
    
    '''
    board looks like
    ((0, 0, 0, 0, 0, 0, 0, 0),
     (0, 0, 0, 0, 0, 0, 0, 0),
     (0, 0, 0, 0, 0, 0, 0, 0),
     (0, 0, 0, 1, 2, 0, 0, 0),
     (0, 0, 0, 2, 1, 0, 0, 0),
     (0, 0, 0, 0, 0, 0, 0, 0),
     (0, 0, 0, 0, 0, 0, 0, 0),
     (0, 0, 0, 0, 0, 0, 0, 0))
    '''
    
    def find_board_edges(board):
        edges = []
        rows = len(board)
        cols = len(board[0])
        for i in range(rows):
            for j in range(cols):
                if i == 0 or i == rows - 1 or j == 0 or j == cols - 1:
                    edges.append((i, j))
        return edges
    
    def find_edge_pieces(board, color):
        edge_pieces = []
        edges = find_board_edges(board)
        for edge in edges:
            if board[edge[0]][edge[1]] == color:
                edge_pieces.append(edge)
        return len(edge_pieces)
    
    def find_corners(board):
        corners = []
        rows = len(board)
        cols = len(board[0])
        corners.append((0, 0))
        corners.append((0, cols - 1))
        corners.append((rows - 1, 0))
        corners.append((rows - 1, cols - 1))
        return corners
    
    def find_corner_pieces(board, color):
        corner_pieces = []
        corners = find_corners(board)
        for corner in corners:
            if board[corner[0]][corner[1]] == color:
                corner_pieces.append(corner)
        return len(corner_pieces)
    
    score = 1 * utility + 1.5 * (find_edge_pieces(board, color) - find_edge_pieces(board, opp)) + 1.5 * (find_corner_pieces(board, color) - find_corner_pieces(board, opp))
    
    return score
    
    
    
    

############ MINIMAX ###############################
def minimax_min_node(board, color, limit, caching = 0):
    # IMPLEMENT!
    """
    A helper function for minimax that finds the lowest possible utility
    """
    # HINT:
    # 1. Get the allowed moves
    # 2. Check if w are at terminal state
    # 3. If not, for each possible move, get the max utiltiy
    # 4. After checking every move, you can find the minimum utility
    # ...
    
    # find opp
    if color == 1:
        opp = 2
    else:
        opp = 1
        
    # check cache
    if (caching) and (board in cache):
        return cache[board] # pull from cache, already got minimax values
    
    # find possible moves
    moves = get_possible_moves(board, opp)
    if len(moves) == 0 or limit == 0:
        return None, compute_utility(board, color)

    min_utility = float('inf')
    best_move = None
    
    for move in moves:
        (col, row) = move # each board
        successor_board = play_move(board, opp, col, row)

        # find utility
        utility = minimax_max_node(successor_board, color, limit - 1, caching)[1]
        
        # check cache
        if caching:
            cache[successor_board] = (move, utility) # load into cache if not already there
        
        # find min utility
        if utility < min_utility:
            best_move = move
            min_utility = utility
    
    return best_move, min_utility


def minimax_max_node(board, color, limit, caching = 0):
    # IMPLEMENT!
    """
    A helper function for minimax that finds the highest possible utility
    """
    # HINT:
    # 1. Get the allowed moves
    # 2. Check if w are at terminal state
    # 3. If not, for each possible move, get the min utiltiy
    # 4. After checking every move, you can find the maximum utility
    # ...
    
    # check cache
    if caching and board in cache:
        return cache[board] # pull from cache, already got minimax values

    moves = get_possible_moves(board, color)
    if len(moves) == 0 or limit == 0:
        return None, compute_utility(board, color)
    
    max_utility = float('-inf')
    best_move = None

    for move in moves:
        (col, row) = move # each board
        successor_board = play_move(board, color, col, row)

        # find utility
        utility = minimax_min_node(successor_board, color, limit - 1, caching)[1]
        
        # check cache
        if caching:
            cache[successor_board] = (move, utility) # load into cache if not already there
        
        # find max utility
        if utility > max_utility:
            best_move = move
            max_utility = utility
    return best_move, max_utility

    
def select_move_minimax(board, color, limit, caching = 0):
    # IMPLEMENT!
    """
    Given a board and a player color, decide on a move using Minimax algorithm. 
    Note that other parameters are accepted by this function:
    If limit is a positive integer, your code should enfoce a depth limit that is equal to the value of the parameter.
    Search only to nodes at a depth-limit equal to the limit.  If nodes at this level are non-terminal return a heuristic 
    value (see compute_utility)
    If caching is ON (i.e. 1), use state caching to reduce the number of state evaluations.
    If caching is OFF (i.e. 0), do NOT use state caching to reduce the number of state evaluations.
    INPUT: a game state, the player that is in control, the depth limit for the search, and a flag determining whether state caching is on or not
    OUTPUT: a tuple of integers (i,j) representing a move, where i is the column and j is the row on the board.
    """
    
    cache.clear()  # clear anything in the cache, good for when we switch from alphabeta to minimax
    
    best_move = minimax_max_node(board, color, limit, caching)[0]
    return best_move


############ ALPHA-BETA PRUNING #####################
def alphabeta_min_node(board, color, alpha, beta, limit, caching = 0, ordering = 0):
    # IMPLEMENT!
    """
    A helper function for alpha-beta that finds the lowest possible utility (don't forget to utilize and update alpha and beta!)
    """
    
    # find opp
    if color == 1:
        opp = 2
    else:
        opp = 1
        
    # check cache
    if (caching) and (board in cache):
        return cache[board] # pull from cache if we have it
    
    moves = get_possible_moves(board, opp)
    if len(moves) == 0 or limit == 0:
        return None, compute_utility(board, color)

    min_utility = float('inf')
    best_move = None
    for move in moves:
        (col, row) = move # each board
        successor_board = play_move(board, opp, col, row)

        # find utility
        utility = alphabeta_max_node(successor_board, color, alpha, beta, limit - 1, caching, ordering)[1]
        
        # check cache
        if caching:
            cache[successor_board] = (move, utility)
        
        if utility < min_utility:
            best_move = move
            min_utility = utility
        
        # a-b pruning
        beta = min(beta, utility)
        if beta <= alpha:
            break
        
    return best_move, min_utility

def alphabeta_max_node(board, color, alpha, beta, limit, caching = 0, ordering = 0):
    # IMPLEMENT!
    """
    A helper function for alpha-beta that finds the highest possible utility (don't forget to utilize and update alpha and beta!)
    """
    
    # check cache
    if (caching) and (board in cache):
        return cache[board] # pull from cache if we have it
    
    moves = get_possible_moves(board, color)
    if len(moves) == 0 or limit == 0:
        return None, compute_utility(board, color)

    if ordering:
        moves = node_ordering_heur(board, moves, color, color)
    
    max_utility = float('-inf')
    best_move = None
    for move in moves:
        (column, row) = move # each board
        successor_board = play_move(board, color, column, row)

        # find utility
        utility = alphabeta_min_node(successor_board, color, alpha, beta, limit - 1, caching, ordering)[1]
        
        # check cache
        if caching:
            cache[successor_board] = (move, utility)
        
        if utility > max_utility:
            best_move = move
            max_utility = utility
        
        # a-b pruning
        alpha = max(alpha, utility)
        if beta <= alpha:
            break
    
    return best_move, max_utility

def select_move_alphabeta(board, color, limit = -1, caching = 0, ordering = 0):
    # IMPLEMENT!
    """
    Given a board and a player color, decide on a move using Alpha-Beta algorithm. 
    Note that other parameters are accepted by this function:
    If limit is a positive integer, your code should enfoce a depth limit that is equal to the value of the parameter.
    Search only to nodes at a depth-limit equal to the limit.  If nodes at this level are non-terminal return a heuristic 
    value (see compute_utility)
    If caching is ON (i.e. 1), use state caching to reduce the number of state evaluations.
    If caching is OFF (i.e. 0), do NOT use state caching to reduce the number of state evaluations.    
    If ordering is ON (i.e. 1), use node ordering to expedite pruning and reduce the number of state evaluations. 
    If ordering is OFF (i.e. 0), do NOT use node ordering to expedite pruning and reduce the number of state evaluations. 
    INPUT: a game state, the player that is in control, the depth limit for the search, a flag determining whether state caching is on or not, a flag determining whether node ordering is on or not
    OUTPUT: a tuple of integers (i,j) representing a move, where i is the column and j is the row on the board.
    """
    
    cache.clear() # clear anything in the cache, good for when we switch from minimax to alphabeta
    
    alpha = float('-inf')
    beta = float('inf')
    best_move = alphabeta_max_node(board, color, alpha, beta, limit, caching, ordering)[0]
    return best_move

####################################################
def run_ai():
    """
    This function establishes communication with the game manager.
    It first introduces itself and receives its color.
    Then it repeatedly receives the current score and current board state until the game is over.
    """
    print("Othello AI") # First line is the name of this AI
    arguments = input().split(",")
    
    color = int(arguments[0]) # Player color: 1 for dark (goes first), 2 for light. 
    limit = int(arguments[1]) # Depth limit
    minimax = int(arguments[2]) # Minimax or alpha beta
    caching = int(arguments[3]) # Caching 
    ordering = int(arguments[4]) # Node-ordering (for alpha-beta only)

    if (minimax == 1): eprint("Running MINIMAX")
    else: eprint("Running ALPHA-BETA")

    if (caching == 1): eprint("State Caching is ON")
    else: eprint("State Caching is OFF")

    if (ordering == 1): eprint("Node Ordering is ON")
    else: eprint("Node Ordering is OFF")

    if (limit == -1): eprint("Depth Limit is OFF")
    else: eprint("Depth Limit is ", limit)

    if (minimax == 1 and ordering == 1): eprint("Node Ordering should have no impact on Minimax")

    while True: # This is the main loop
        # Read in the current game status, for example:
        # "SCORE 2 2" or "FINAL 33 31" if the game is over.
        # The first number is the score for player 1 (dark), the second for player 2 (light)
        next_input = input()
        status, dark_score_s, light_score_s = next_input.strip().split()
        dark_score = int(dark_score_s)
        light_score = int(light_score_s)

        if status == "FINAL": # Game is over.
            print
        else:
            board = eval(input()) # Read in the input and turn it into a Python
                                  # object. The format is a list of rows. The
                                  # squares in each row are represented by
                                  # 0 : empty square
                                  # 1 : dark disk (player 1)
                                  # 2 : light disk (player 2)

            # Select the move and send it to the manager
            if (minimax == 1): # run this if the minimax flag is given
                movei, movej = select_move_minimax(board, color, limit, caching)
            else: # else run alphabeta
                movei, movej = select_move_alphabeta(board, color, limit, caching, ordering)
            
            print("{} {}".format(movei, movej))


if __name__ == "__main__":
    run_ai()
