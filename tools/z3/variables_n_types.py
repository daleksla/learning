"""
    * @brief File shows how to create variables of different types in z3 and effects of such use when solving

    * To create variables:
        * Create single variable: <type>(<string_z3_should_refer_to_var_as>)
        * Create multiple variables of a given type: <type>s(<string_containing_space_seperated_names_z3_should_refer_to_vars_as)
            * Returns tuple of said objects
        * Convention to store output of these calls into variable of the same as what you told z3 to call said variable

    * Multiple different types in z3:

        * Bool, Int, Real, Array, List, Funnctions (see function_reasoning.py)
            * non-whole numbers and related calculating do not suffer inaccuracy
                * z3 internally uses fractions and other methods to precisely store values.
                * when printing, it is done in floating point format - the `?` at the end of the float flags this as just an approximation to the actual data
                * We can set precision of decimal output using the `set_option` *function* with the `precision` parameter set
                * furthermore, we can derive the actual expression using the .spexr() method on the z3 datatype
            * Note: since polynomial equations have solutions for rational and irrational->algebraic numbers ONLY, z3 does not values such as PI and e as these are irrational->transcendental values
            * Note: numbers such as √2 are stored as 'root objects' when represented, storing a polynomial and a number showing which root we are talking about (as any number has two square roots)

        * Z3 requires us to specify the domains of our variables clearly - it affects what algorithms are run by Z3 and the subsequent results
            * e.g. if a problem can only be satisified with real numbers but the variable in the constraints were integers, solver would still fail as you specified you want integers as part of the constraint

"""

import z3

"""
    * @brief type_importance_example - function to show how example of how solver acts given variables of certain datatypes
    * @param Function - constructor / function to create either an Int or Real variable
"""
def type_importance_example(real_or_int):
    x = real_or_int('x') # create z3 Real/Int object which will be known by z3 internally by identifier x
    y = real_or_int('y') # create z3 Real/Int object which will be known by z3 internally by identifier y

    s= z3.Solver()
    s.add(y > 0)
    s.add(x + 3 * y == 1)
    s.add(x == -y)

    if s.check() == z3.sat: # <solver_obj>.check method solves the asserted constraints, see feasibility
        print(s.model()) # print entire solved model
    else:
        print("Problem unsatisifiable :\'(")

"""
    * @brief decimal_point_precision - shows how z3 manages decimal / non-whole values with accuracy
"""
def decimal_point_precision():
    x = z3.Sqrt(2)
    print("Maintained expression form:", x.sexpr())

def main():
    print("Using Int variables, which may act as a constraint: ", end="\n\t") # ints are +/- whole numbers ONLY
    type_importance_example(z3.Int)

    print("Using Real variables which are more flexible then ints: ", end="\n\t") # reals are *any* number from -inf -> +inf
    type_importance_example(z3.Real)

    decimal_point_precision()


if __name__ == "__main__":
    main()
