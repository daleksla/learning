{-
  This is the file variables.hs
  In this file will be examples of creating and showing basic usage of variables
  Summary:
    * Creating: <variable_name> = <data>
        * Use variables anywhere you would use data.
            * Note: placeholder data `undefined` triggers error upon actually being used in a computed expression
        * 'let' expression can be used to define binding names locally. Benefit is that an expression can use a placeholder within the expression and then the name would be 'free' to then be actually used elsewhere
    * Variables are immutable and can't be changed (more like defines to be substituted) (theyre more like names or bindings etc.)
        * Note: an interpretter won't complain because it messes with the scoping to allow for multiple definitions (not redefinitions etc.)
        
-}

-- creating variables
num = 1
num2 = undefined -- note: placeholder data.

-- using variables
show num -- use them anywhere
num `min` num
-- show num2 -- ERROR. Note: triggers error as placeholder was not redefined by sensible value. lazy evaluation demonstration
z = num + num2 -- note: whilst this is NOT evaluated (just saved as its not actual computation)
-- z  -- ERROR. note: now causes error

a = 4 * (let a = 9; b=10; c=11 in a + b + c - 1) + 2 -- 118 . note: within brackets, bindings / names a, b c are created and then used. beyond those brackets the three variables go out of scope and are then free to use again, hence the variable name is a
