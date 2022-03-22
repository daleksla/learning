"""
    * @brief File demonstrates the bare basics of how to solve a given problem using the Python z3 API

     * Using the z3 solver:
        * Initialise an object: z3.Solver()
        * Add constraints:
            * Syntax: <solver_obj>.add(<constraint>)
            * The constraint typically involve one or more z3 variables created
                * z3 uses its own datatypes (as opposed to native Python types)
                * see types.py for a better analysis of how z3 manages these
                * z3 will actually tell you what these variables ended up being set as, so they're needed
        * Solve constraints: <solver_obj>.check()
            * Returns z3.sat when then can be satisfied - in that case you can view the satisfying assignment with a call to model (which is what solve prints).
            * Returns z3.unsat when Z3 has determined that it is absolutely impossible to satisfy all these constraints together.
            * Returns z3unknown when Z3 could not decide either way (e.g. time out or no suitable algorithm implemented).

        * Getting results:
            * to show all the values in the satisfied model: <solver_obj>.model()
            * calling <solver_obj>.model() BEFORE <solver_obj>.check() will cause an exception
"""

import sys
import z3 # z3 module

def basics():
    x = z3.Int('x') # create z3 object which will be known by z3 internally by identifier x

    s = z3.Solver() # create solver object
    s.add((x) ** 3 < 300) # one by one, add constraints
    s.add((x) ** 2 > 25)
    s.add(x >= 0)
    s.add(x % 2 == 0)

    if s.check() == z3.sat: # <solver_obj>.check method solves the asserted constraints, see feasibility
        print(s.model()) # print entire solved model
    else:
        print("Problem unsatisifiable :\'(")

if __name__ == "__main__":
    basics()
