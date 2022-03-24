import z3

"""
	* @brief Using knights-and-knaves as an example of real z3 and constraint programming usage

    * Knaves lie, knights are honest
	* Q: "A claims both he and B are knaves", is this true?
"""

# crete variables and constraints
a = z3.Bool("a") # person a
b = z3.Bool("b") # person b

# note: we say knave is false (since they always lie) and knight is true
a_claim = z3.And(a == False, b == False) # A claims both he and B are knaves

formula = (a == False) == (a_claim == False)
# if a is truly a knave, his claim should be false

# create solver
s = z3.Solver()
s.add(formula)
if s.check() == z3.sat:
	print("Determined model:", s.model())
else:
	print("What the hell have u done wrong")
