"""
    * @brief File demonstrates how to mathematically solve problems in z3

    * z3 is a tool to prove satisfiability
        * This reflects in it's usage of the term 'solve' - to solve whether a given problem is satisfiable by doing the minimum and determining only soltuion which can satisfy the problem (existential quantification on all the variable)
        * Mathematically, solving is to find ALL solutions for a given problem
    * It is trivial to make z3 mathematically solve such problems - simply keep adding, as a constraint, that the answer it comes up with cannot be equal to the previous determination
"""

import sys
import z3 # z3 module

def basics():
    x = z3.Int('x') # create z3 object which will be known by z3 internally by identifier x

    s = z3.Solver() # create solver object
    s.add((x) ** 3 < 300) # one by one, add constraints
    s.add(x > 0)
    s.add(x % 2 == 0)

    if s.check() == z3.sat: # <solver_obj>.check method solves the asserted constraints, see feasibility
        print("Possible values of x:", end=" ")
        while s.check() == z3.sat:
            print(s.model()[x], end=" ") # print the value of x ONLY
            s.add(x != s.model()[x]) # prevent next model from using the same assignment as a previous model
    else:
        print("Problem unsatisifiable :\'(")
    print()

if __name__ == "__main__":
    basics()
