import z3

"""
	* @brief Using product purchase problem as an example of real z3 and constraint programming usage

    * Our business requires resources of three types of resource: products A, B and C. We have £100 and want to purchase as many product A as possible
    * For every type A product we purchase we must purchase two type B products;
    * For every type B product we purchase we must purchase four type C products.
    * Product A costs £5 each, product B costs £1 each, and product C costs 50 pence each.
    * Q: What is the maximum number of product A we can buy?
"""

# define variables and constants
A_COST = 500 # £5
B_COST = 100 # £1
C_COST = 50 # 50p / £.5
TOTAL_COST = 10000 # £100
a_count, b_count, c_count = z3.Ints("a_count b_count c_count")

# define constraints
s = z3.Solver()

s.add(a_count * 2 == b_count) # there should be twice the amount of B producta for each A product
s.add(b_count * 4 == c_count) # there should be four times the amount of C products for each B product
s.add((a_count * A_COST) + (b_count * B_COST) + (c_count * C_COST) <= TOTAL_COST) # note: in pennies

largest_a = 0
model = 0
while s.check() == z3.sat:
	model = s.model()
	largest_a = model[a_count]
	s.add(a_count > largest_a)

print("Final model with highest A:", model)
