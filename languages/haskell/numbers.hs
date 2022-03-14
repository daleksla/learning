{-
    This is the file numbers.hs
    In this file will be examples of basic standard numeric expressions and arithmetic
    Note: surrounding curly braces with a suceeding and preceeding hyphens inbetween serve as multi-line comment blocks

    Summary:

        * Operators: +, -, /, *

        * Different types of numbers: float, fractional, int. Note: cannot apply all operations across all types (ie. Int and Fractionals can't divide by each other) (see typeclasses.hs for a detailed look into the system these numbers use as well as what haskell uses to create abstract types)
-}

-- Following are examples of basic numerical expressions (including arithmetic)
-- note: double hyphens initialises a comment which eats up the rest of the given line
3.0 -- 3.0. note: cannot suffix float with .f like in C, etc.
123+456 -- 579.
4-7 -- -3.
0.5*730/10 -- 36.5. note: 0.5 cannot be written .5
0.1+0.2 -- 0.30000000000000004. note: classic example of the struggles of floating point arithmetic
5*(-3) -- -15. note: haskell will throw an error if you get rid of the brackets.
pi * 1 -- 3.141592653589793. note: haskell contains many constants for on-demand use, such as pi. It is a type of variable, which we'll look at later

::type 3.14 -- Fractional. Note: fractional means all numbers with post decimal bits. float is an INSTANCE of the fractional typeclass. fractional is default until specified / forced otherwise
123::Float --  note: here we FORCE haskell to make 123 a float rather than allow it to deduce it as an int, permanenetly.
-- 123::Float + 1::Int -- ERROR. note: cannot cast values explicitly defined
:info Float --  note: shows what operations have been allowed for the Float typeclass
