{-
  This is the file numbers.hs
  In this file will be examples of standard numeric expressions and arithmetic
  Note: surrounding curly braces with a suceeding and preceeding hyphens inbetween serve as multi-line comment blocks
-}

-- Following are examples of basic numerical expressions (including arithmetic)
-- note: double hyphens initialises a comment which eats up the rest of the given line
3.0 -- 3.0. note: cannot suffix float with .f like in C, etc.
123+456 -- 579.
4-7 -- -3.
0.5*730/10 -- 36.5. note: 0.5 cannot be written .5
0.1+0.2 -- 0.30000000000000004. classic example of the struggles of floating point arithmetic
5*(-3) -- -15. haskell will throw an error if you get rid of the brackets.
pi * 1 -- 3.141592653589793. note: haskell contains many constants for on-demand use, such as pi. It is a type of variable, which we'll look at later