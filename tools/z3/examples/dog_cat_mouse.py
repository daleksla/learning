import z3

"""
	* @brief Using dog-cast-mouse buying as an example of real z3 and constraint programming usage

	* must spend 100 pounds for 100 animals
    * dogs = £15, cat = £1, mice = £.25 (25p)
    * must buy one of each
    * Q: what numbers of each do I end up having to buy
"""

# variables - note: we're using integers so cannot introduce fractorials / non-integers - know this!
# DOG_COST = 15
# CAT_COST = 1
# MICE_COST = .25 -- this is in pounds but leads to fractorial which will screw up the algorithm . convert to pennies
DOG_COST = 1500
CAT_COST = 100
MICE_COST = 25 # this is in pennies which is int hence valid
TOTAL_COST = 10000
dog_count, cat_count, mice_count = z3.Ints("dog_count cat_count mice_count")

# solver and constraints
s = z3.Solver()

s.add(dog_count >= 1)
s.add(cat_count >= 1)
s.add(mice_count >= 1)
s.add((dog_count * DOG_COST) + (cat_count * CAT_COST) + (mice_count * MICE_COST) == TOTAL_COST) # note: in pennies

# check satisfiability
if s.check() == z3.sat:
	print("Model:", s.model())
