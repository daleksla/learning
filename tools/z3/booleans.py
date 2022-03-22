"""
    * @brief File shows how to add boolean logic into / as constraints

    * In order to form a logical statement we need the z3 equivalent of the Boolean logic operators: And, Or, Not
        * There is also the function Implies (also known as if and only if)
        * Normal Python and / or / not cannot be used to perform Boolean expressions

"""

import z3

def boolean_solver():
    p = z3.Bool('p')
    q = z3.Bool('q')
    r = z3.Bool('r')
    z3.solve(z3.Implies(p, q), r == z3.Not(q), z3.Or(z3.Not(p), r)) # ( p ⇒ q ) ∧ ( r = ¬q ) ∧ ( ¬p ∨ r )

if __name__ == "__main__":
    boolean_solver()
