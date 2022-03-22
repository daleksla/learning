"""
    * @brief File demonstrates the how to alter the Solver object

    * Solver object has several inbuilt methods to manage constraints
        * add - declares a new constraint
        * pop - remove most-recent added benchmark / scope and it's associated constraints
        * push - sets benchmark / creates a new scope
        * *Why do I care?* In some applications, we want to explore several similar problems that share several constraints and it is better to make use of an object which has performed these computations already, thereby not repeating computations already performed just because we add / new constraint(s)
            * Use method `statistics` to get performance statistics done by a given solver

    * Value extraction
        * To show the result of a single variable, index the model object returned by the model method of the solver: <solver_obj>.model()[<python_variable_of_z3_obj>]
        * The public `evaluate` attribute (ie. <solver_obj>.evaluate) contains ALL values (in order of what was given) stored by the solver - this can be used to simply automatically map all the values it contains onto another tuple of variables
        * Note: in both cases, these operations will produce z3 datatype

"""

import sys
import z3 # z3 module

"""
    * @brief efficient_solver - demonstrates manipulation of inner constraints

    * Starts by adding one constraint, solving
    * Sets up new scope, adds another constraint and solves it
    * Removes scope and its associated constraints and ask for solving - it will just show what has been precalculated
"""
def efficient_solver():
    s = z3.Solver()
    x = z3.Int('x')
    y = z3.Int('y')

    s.add(x > 10, y == x + 2)
    print(s)
    print("Solving constraints in the solver s ...")
    isSAT = s.check()
    print(isSAT)

    print("Create a new scope...")
    s.push()

    print("Solving updated set of constraints...")
    s.add(y < 11)
    isSAT = s.check()
    print(isSAT)
    if isSAT == z3.sat:
        print(s.model())
    print("Performance statistics: ", s.statistics())
    old_stats = s.statistics()

    print("Restoring state...")
    s.pop()

    print("Solving previously-done set of constraints...")
    isSAT = s.check()
    print("Performance statistics: ", s.statistics())
    print("Has extra solving been done (comparing statistics): ", old_stats == s.statistics())

"""
    * @brief value_retrieval - demonstrates value extraction from solver
"""
def value_retrieval():
    s = z3.Solver()
    x = z3.Int('x')
    y = z3.Int('y')
    s.add(x > 10, y == x + 2)
    s.check()
    m = s.model()

    x = m[x] # get value of x and overwrite old type
    print(x)

    sol = list(map(m.evaluate, (x,y)))
    print(sol)


def main():
    efficient_solver()
    value_retrieval()


if __name__ == "__main__":
    main()
