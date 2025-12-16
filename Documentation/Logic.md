# Logic

> Here I do some records for my project report. Because I think I have run across some troubles when I 
> do the lab. So I do some explaination for the future I have recall the project.

[Documentation Address](https://inst.eecs.berkeley.edu/~cs188/sp24/projects/proj3/#q4-3-points-path-planning-with-logic)


## Q3 Pacphysics and Satisfiability

Actually, this question is used to let us implement the following functions:

- `pacmanSuccessorAxiomSingle`
- `pacphysicsAxioms`
- `checkLocationSatisfiability`

I have read the documentation for have trouble in understanding what do the author wants me to do.
 Simply, it is a simple question. It uses the logical axiom to represents the pacman's physical **action** and **state**.

Here are some examples:

### `pacmanSuccessorAxiomSingle`

```python
# noinspection PyUnresolvedReferences
def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness
    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last)
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    current_pos = PropSymbolExpr(pacman_str, x, y, time = now)
    possible_causes_ : Expr = disjoin(possible_causes)
    return current_pos % possible_causes_
```

We look the above code block, we can find that the function given the following parameters:

- `x` the x-coord of the pacman
- `y` the y-coord of the pacman
- `time` the current timestep
- `walls_grid` the distribution of the wall in the problem

and the output is an instance of the `Expr`,which an expression represents the all the possible **location** && **action** where the pacman can start from in  `time - 1`

### `pacphysicsAxioms`

```python
# noinspection PyUnresolvedReferences
def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    pacphysics_sentences = []

    "*** BEGIN YOUR CODE HERE ***"
    # The First Constraint If (x, y) is the wall that, it mustn't be the position which pacman can be
    # wallAt(x, y) -> ~PacmanAt(x, y)
    # wallList used to store the sentences that it doesn't exist the pacman at (x, y)
    for (x, y) in all_coords:
        wall_at_xy = PropSymbolExpr(wall_str, x, y)
        pacman_at_xy_t = PropSymbolExpr(pacman_str, x, y, time = t)
        pacphysics_sentences.append(wall_at_xy >> ~pacman_at_xy_t)

    # Pacman is at exactly one of the non-wall position at time t
    pacman_at_position = [PropSymbolExpr(pacman_str, x, y, time = t) for (x, y) in non_outer_wall_coords]
    pacphysics_sentences.append(exactlyOne(pacman_at_position))

    # Pacman takes exactly one action at time t
    pacman_actions = [PropSymbolExpr(action, time=t) for action in DIRECTIONS]
    pacphysics_sentences.append(exactlyOne(pacman_actions))

    # Sensor model axioms (if provided)
    if sensorModel is not None:
        pacphysics_sentences.append(sensorModel(t, non_outer_wall_coords))

    # sucessorAxioms
    if t > 0 and successorAxioms is not None:
        pacphysics_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))

    "*** END YOUR CODE HERE ***"

    return conjoin(pacphysics_sentences)
```

actually, it is the same. The above problem need us to analysis all the possible for the **position** and **action** in time `t`

- `wallAt(x, y) -> ~PacmanAt(x,y)` it indicates that at the position `(x, y)` there mustn't be the wall position
- try to use the `exactlyOne` function to get the cases that everytime the pacman exactly can in the one position/ do one action.



## Q4 Path Planning with logic

- input:
  - Problem
    - `startState` $x_0, y_0$
    - `goalState` $x_g, y_g$
    - `wallgrid`

you do not need to implement the search algorithm. 
**But used the traditional enumeration all the possible position and action and findModel to vertify whether the result exists**


Show the Code:

```python
# noinspection PyUnresolvedReferences
def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    # Here we used the non_wall_coords;
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []
    "*** BEGIN YOUR CODE HERE ***"
    # initial knowledge
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time = 0))
    # we do the loop for 1 - 50 timestamps;
    for t in range(50):
        print(f"Now it is timestamp: {t}")
        # in time = t, the pacman is exactly can be one direction;
        # Step1 : we enumerate all the possible position of non_wall_coors
        pacman_at_position = [PropSymbolExpr(pacman_str, x, y, time = t) for (x, y) in non_wall_coords]
        KB.append(exactlyOne(pacman_at_position))
        # Step2 : pacman can take one action at each timestamp
        KB.append(exactlyOne([PropSymbolExpr(action, time=t) for action in actions]))
        # Add transition model sentences for pacman positions
        for (x, y) in non_wall_coords:
            transition_axiom = pacmanSuccessorAxiomSingle(x, y, t+1, walls_grid)
            if transition_axiom:
                KB.append(transition_axiom)

        goal_assertion = PropSymbolExpr(pacman_str, xg, yg, time = t)
        model = findModel(conjoin(KB + [goal_assertion]))

        if model:
            return extractActionSequence(model, actions)
    "*** END YOUR CODE HERE ***"
    return []
```

The detailed description for this function's implementation is in the documentation. Actually, in the simple says that we just
enumerate all the possible position and action in the loop (`for t in range(50)`)

**what we infer is the process time `t` from `t + 1`**