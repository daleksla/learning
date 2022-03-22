"""
    * @brief File shows has z3 can analyse functions

    * Functions are defined as z3 objects using the `Function()` constructor
        * Takes 3 params minimum:
            * #1 is name of variable z3 will reference (same as normal z3 data value constructors)
            * #2, ..., n-1 are data type going in (domain)
            * #n is data type going out (codomain)
        * #2 and #3 can be IntSort(), BoolSort(), etc..

    * We can create constraints related to a given function regarding its inputs and outputs

    * Constraint solving a function involves determining the feasibility of these arguments
        * Note: these functions must be approached in the mathematical sense (ie. no side effects, no exceptions, computation defined solely based on input values)
        * Just like the SAT/SMT solver produces the possible value variables may evaluate to, said solver for functions predicts a possible body (of the function)

    * The interpretation given to an undefined function is stored in the model and therefore can be accessed and even executed as a function
        * Note: to extract the determined function body: <model>[<function_object>]
        * Note: to extract the VALUE of a given call, use model.evaluate, passing a call to the function object
            * Syntax: <model>.evaluate(<function_object>(args...))

"""

import z3

def function_reasoning():
    x = z3.Int('x')
    y = z3.Int('y')
    f = z3.Function('f', z3.IntSort(), z3.IntSort()) # function which takes a single int as a parameter, returns a single int

    s = z3.Solver()
    s.add(f(x) == x)
    s.add(f(y) == y)
    s.add(x != y) # constraints saying that when function takes in variable x, it returns x, when it takes variable y, it returns y and x doesnt equal y

    s.check()
    model = s.model()
    print("Model determined: ", model)
    print("Getting determined function body: ", model[f]) # extract from model, call function
    print("Getting determined function output when ran with arg of 42: ", model.evaluate(f(42))) # extract from model, call function

if __name__ == "__main__":
    function_reasoning()
