# search.py
# ---------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""
import util
from game import Directions
from typing import List

from util import Stack, Queue, PriorityQueue


class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem: SearchProblem) -> List[Directions]:
    
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    
    s = Directions.SOUTH
    w = Directions.WEST
    
    return  [s, s, w, s, w, w, s, w]


def depthFirstSearch(problem: SearchProblem) -> List[Directions]:
    """
    Search the deepest nodes in the search tree first.

    Your search algorithm needs to return a list of actions that reaches the
    goal. Make sure to implement a graph search algorithm.

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:

    print("Start:", problem.getStartState())
    print("Is the start a goal?", problem.isGoalState(problem.getStartState()))
    print("Start's successors:", problem.getSuccessors(problem.getStartState()))
    """
    "*** YOUR CODE HERE ***"
    # Now we get the start_state
    stack_ = Stack()
    # Used to store for the nodes that we have visited
    visited_states = set()

    start_state = problem.getStartState()
    start_path = []
    # We Start for store the state and start_path
    stack_.push((start_state, start_path))

    while stack_:
        # Start For DFS
        current_node, action_path = stack_.pop()

        if problem.isGoalState(current_node):
            return action_path

        if current_node in visited_states:
            continue

        visited_states.add(current_node)
        successors = problem.getSuccessors(current_node)

        for successors_state, action_to_successor, _ in successors:
            if successors_state not in visited_states:
                new_actions_path = action_path + [action_to_successor]
                stack_.push((successors_state, new_actions_path))

    return []

def breadthFirstSearch(problem: SearchProblem) -> List[Directions]:
    """Search the shallowest nodes in the search tree first."""
    "*** YOUR CODE HERE ***"
    queue_ = Queue()

    start_state = problem.getStartState()
    visited_state = set()

    start_path = []
    queue_.push((start_state, start_path))

    while queue_:
        # Start for the BFS
        node, path = queue_.pop()
        # Find the final node
        if problem.isGoalState(node):
            return path

        if node in visited_state:
            continue
        visited_state.add(node)
        successors = problem.getSuccessors(node)

        for successors_state, action_to_state, _ in successors:
            if successors_state not in visited_state:
                path_ = path + [action_to_state]
                queue_.push((successors_state, path_))

    return []

def uniformCostSearch(problem: SearchProblem) -> List[Directions]:
    """Search the node of least total cost first."""
    # Here PriorityQueue we store for the action cost as the priority
    "*** YOUR CODE HERE ***"
    pq = PriorityQueue()
    # We should store for a node
    # This the distance to the start node with its path
    ucsMap = {}

    start_state = problem.getStartState()
    start_action = []
    pq.push((start_state, start_action, 0),0)
    ucsMap[start_state] = (start_action, 0)

    while pq:
        # we take a node from the pq everytime
        state, action, cost = pq.pop()

        # if we find the goal state
        if problem.isGoalState(state):
            return action

        successor = problem.getSuccessors(state)
        for next_successor, action_, cost_ in successor:
            # for every node we test
            current_action = action + [action_]
            new_cost = cost + cost_
            if next_successor not in ucsMap or (new_cost < ucsMap[next_successor][1]):
                ucsMap[next_successor] = (current_action, new_cost)
                pq.push((next_successor, current_action, new_cost), new_cost)

    return []

def nullHeuristic(state, problem=None) -> float:
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0

def aStarSearch(problem: SearchProblem, heuristic=nullHeuristic) -> List[Directions]:
    """Search the node that has the lowest combined cost and heuristic first."""
    "*** YOUR CODE HERE ***"
    pq = PriorityQueue()
    # Used to store for the path && cost
    aStarMap = {}

    start_state = problem.getStartState()
    start_action = []
    # There is one thing that we need to get know is that the position is recorded in the
    # First Postion of the state
    mandistance = heuristic(start_state, problem)
    pq.push((start_state, start_action, 0), mandistance)
    aStarMap[start_state] = (start_action, 0)

    while pq:
        # we take a node from the pq with the lowest priority
        node_, action_, cost_ = pq.pop()

        # base case
        if problem.isGoalState(node_):
            return action_

        successors = problem.getSuccessors(node_)
        for next_, next_action_, next_cost in successors:
            new_manDistance = next_cost + cost_ + heuristic(next_, problem)
            new_action = action_ + [next_action_]

            if next_ not in aStarMap or (aStarMap[next_][1] > next_cost + cost_):
                aStarMap[next_] = (new_action, next_cost + cost_)
                pq.push((next_, new_action, next_cost + cost_), new_manDistance)
    return []

# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
