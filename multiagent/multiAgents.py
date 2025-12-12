# multiAgents.py
# --------------
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


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent
from pacman import GameState

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState: GameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        # Actually, we need to modify the evaluationFunction with the specific action
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState: GameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed successor
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (newFood) and Pacman position after moving (newPos).
        newScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()
        newFood = successorGameState.getFood()
        newGhostStates = successorGameState.getGhostStates()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]
        "*** YOUR CODE HERE ***"

        x, y = newPos
        FoodPos = newFood.asList()

        minDistance = 1
        # We assume the score1 for the minDistance to the Food which has not Eaten
        # This is the weight of the distance between the pacman with the pellt
        w1 = 10.0
        # This is the weight of the number of the rest-pellts
        w2 = -500.0
        # This is the weight of the distance of the ghost
        # Only when the distance <= 2 it will do factor
        w3 = -100000.0
        # This is the weight of the base score
        w4 = 100.0
        w5 = 10.0

        if len(FoodPos) > 0:
            minDistance = min([util.manhattanDistance(newPos, food) for food in FoodPos])

        if minDistance == 0:
            minDistance = 1

        count = len(FoodPos)

        flag = False
        minGhostDistance = 100000
        index = 0
        for i in range(len(newGhostStates)):
            ghost = newGhostStates[i]
            gx, gy = ghost.getPosition()
            distance = abs(gx - x) + abs(gy - y)
            if distance < minGhostDistance:
                minGhostDistance = distance
                index = i
                if distance < 2 and newScaredTimes[i] == 0:
                    flag = True
                    break

        sum_ = w1 * (1 / minDistance) + w2 * count + (w3 if flag else (newScaredTimes[index] * w5)) + w4 * successorGameState.getScore()

        return sum_
def scoreEvaluationFunction(currentGameState: GameState):
    """
    This default evaluation function just returns the score of the state.
    The score is the same one displayed in the Pacman GUI.

    This evaluation function is meant for use with adversarial search agents
    (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
    This class provides some common elements to all of your
    multi-agent searchers.  Any methods defined here will be available
    to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

    You *do not* need to make any changes here, but you can if you want to
    add functionality to all your adversarial search agents.  Please do not
    remove anything, however.

    Note: this is an abstract class: one that should not be instantiated.  It's
    only partially specified, and designed to be extended.  Agent (game.py)
    is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)

class MinimaxAgent(MultiAgentSearchAgent):
    """
    Your minimax agent (question 2)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action from the current gameState using self.depth
        and self.evaluationFunction.

        Here are some method calls that might be useful when implementing minimax.

        gameState.getLegalActions(agentIndex):
        Returns a list of legal actions for an agent
        agentIndex=0 means Pacman, ghosts are >= 1

        gameState.generateSuccessor(agentIndex, action):
        Returns the successor game state after an agent takes an action

        gameState.getNumAgents():
        Returns the total number of agents in the game

        gameState.isWin():
        Returns whether or not the game state is a winning state

        gameState.isLose():
        Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        score, action = self.value(gameState, 0, 0)
        return action

    def value(self, gameState: GameState, agentIndex, currentDepth):
        # base case
        if gameState.isLose() or gameState.isWin():
            return self.evaluationFunction(gameState), Directions.STOP

        if currentDepth == self.depth:
            return self.evaluationFunction(gameState), Directions.STOP
        # select for which the agent will be the next
        numAgents = gameState.getNumAgents()
        nextAgentIndex = (agentIndex + 1) % numAgents
        # count for the next Depth
        nextAgentDepth = currentDepth + 1 if nextAgentIndex == 0 else currentDepth
        legalActions = gameState.getLegalActions(agentIndex)

        if agentIndex == 0:
            return self.max_value(gameState, legalActions, nextAgentIndex, nextAgentDepth)
        else:
            return self.min_value(gameState, agentIndex, legalActions, nextAgentIndex, nextAgentDepth)


    def max_value(self, gameState, legalActions, nextAgentIndex, nextDepth):
        # we should return the max value of the legal Actions;
        bestScore = -float('inf')
        bestAction = Directions.STOP

        for action in legalActions:
            successor = gameState.generateSuccessor(0, action)

            score, _ = self.value(successor, nextAgentIndex, nextDepth)

            if score > bestScore:
                bestScore = score
                bestAction = action
        return bestScore, bestAction

    def min_value(self, gameState, agentIndex, legalActions, nextAgentIndex, nextDepth):
        # we should return the min value of the legal Actions;
        bestScore = float('inf')
        bestAction = Directions.STOP

        for action in legalActions:
            successor = gameState.generateSuccessor(agentIndex, action)

            score, _ = self.value(successor, nextAgentIndex, nextDepth)

            if score < bestScore:
                bestScore = score
                bestAction = action

        return bestScore, bestAction

class AlphaBetaAgent(MultiAgentSearchAgent):
    """
    Your minimax agent with alpha-beta pruning (question 3)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action using self.depth and self.evaluationFunction
        We add 2 params in the max_value and min_value
        """
        "*** YOUR CODE HERE ***"

        # alpha represent the maximum value of the MAX-Layer
        # beta represents the minimum value of the MIN-Layer
        alpha = -1 * float("inf")
        beta = float("inf")
        score, action = self.value(gameState,0, 0, alpha, beta)
        return action

    def value(self, gameState: GameState, agentIndex, currentDepth, alpha, beta):
        # base case
        if gameState.isLose() or gameState.isWin():
            return self.evaluationFunction(gameState), Directions.STOP
        # if the currentDepth == self.depth
        if currentDepth == self.depth:
            return self.evaluationFunction(gameState), Directions.STOP

        numAgent = gameState.getNumAgents()
        nextAgentIndex = (agentIndex + 1) % numAgent

        nextAgentDepth = currentDepth + 1 if nextAgentIndex == 0 else currentDepth
        legalActions = gameState.getLegalActions(agentIndex)

        if agentIndex == 0:
            return self.max_value(gameState, legalActions, nextAgentIndex, nextAgentDepth, alpha, beta)
        else:
            return self.min_value(gameState, legalActions, agentIndex, nextAgentIndex, nextAgentDepth, alpha, beta)

    # Helper function used to
    def max_value(self, gameState: GameState, legalActions, nextAgentIndex, nextDepth, alpha, beta):
        bestscore = -1 * float("inf")
        bestAction = Directions.STOP

        for action in legalActions:
            successor = gameState.generateSuccessor(0, action)

            score, _ = self.value(successor, nextAgentIndex, nextDepth, alpha, beta)

            if score > bestscore:
                bestscore = score
                bestAction = action

            # pruning
            if bestscore > beta:
                return bestscore, bestAction

            alpha = max(alpha, bestscore)

        return  bestscore, bestAction

    def min_value(self, gameState: GameState, legalActions, agentIndex, nextAgentIndex, nextDepth, alpha, beta):
        bestscore = float("inf")
        bestAction = Directions.STOP

        for action in legalActions:
            successor = gameState.generateSuccessor(agentIndex, action)

            score, _ = self.value(successor, nextAgentIndex, nextDepth, alpha, beta)

            if score < bestscore:
                bestscore = score
                bestAction = action

            # pruning
            if bestscore < alpha:
                return bestscore, bestAction

            beta = min(beta, bestscore)

        return bestscore, bestAction

class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 4)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the expectimax action using self.depth and self.evaluationFunction

        All ghosts should be modeled as choosing uniformly at random from their
        legal moves.
        """
        "*** YOUR CODE HERE ***"
        util.raiseNotDefined()

def betterEvaluationFunction(currentGameState: GameState):
    """
    Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
    evaluation function (question 5).

    DESCRIPTION: <write something here so we know what you did>
    """
    "*** YOUR CODE HERE ***"
    util.raiseNotDefined()

# Abbreviation
better = betterEvaluationFunction
