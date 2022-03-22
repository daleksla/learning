"""
    * @brief File demonstrates how to perform validiation using the z3 SAT/SMT solver

    * z3 is a tool to prove satisfiability of a given constraint (ie finds an *instance* of an assignment to a variable such that the constraint evaluates to true)
    * Validity however is where a constraint, not matter the assignments made, always evaluates to true
    * z3 *can* be used to validate constraints by simply determining whether the NOT of a constraint is ever false - if it ever is, then it is not validated


"""

import sys
import z3 # z3 module

"""
    * @brief validate - takes in constraint, creates solver and attempts to validate by NOT'ing the constraints
    * @param f - z3 constraint
"""
def validate(f):
    s = z3.Solver()
    s.add(z3.Not(f))
    if s.check() == z3.unsat:
        print("validated")
        return True
    else:
        print("failed to validate")
        return False

"""
    * @brief demorgans_law - example of validation
    * function attempts to validate demorgans law by checking the validity of the two statements it declares
"""
def demorgans_law():
    x = z3.Bool("x")
    y = z3.Bool('y')
    demorgans_law_1 = z3.And(z3.Not(x), z3.Not(y)) == z3.Not(z3.Or(x, y)) # (¬P) ∧ (¬Q) == ¬( P ∨ Q ) -- statement 1
    demorgans_law_2 = z3.Or(z3.Not(x), z3.Not(y)) == z3.Not(z3.And(x, y)) # (¬P) ∨ (¬Q) == ¬( P ∧ Q ) -- statement 2
    print("Is demorgans law valid?: ", validate(demorgans_law_1) and validate(demorgans_law_2))

if __name__ == "__main__":
    demorgans_law()
