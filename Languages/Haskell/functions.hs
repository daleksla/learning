{-
    This is the file functions.hs
    Functions are a central concept in Haskell - they are the default command / operation assumed unless an operator etc. is found appropriately
    In this file contains examples of calling and writing functions
    Summary: Calling: <function_name> arg1 ... argn . Writing: <function_name> arg1 ... argn = <func_body> . Function names need to be lowercase. Body of functions is singularly expression. 
-}

-- following is an example of calling functions
putStrLn "hi" --  note: parantheses are NOT required for a function call. putStrLn is the function name, "hi" is a string provided as an argument
44 - 33 --  note: basically everything in Haskell which fits for an operation is a function call. this in an example of an 'inifix function'. To call an infix function, it just needs to be a function which takes in two arguments, with the one arg on each side
44 `min` 33 --  note: the subtraction operator is called as an 'infix function' called min. call it as above
show (min 44 33) --  note: this example shows the output (as a string) of the result returning by 44 - 33. nested function call

-- following is an example of defining a function
-- THEY MUST start with a lower case letter OR an underscore
-- They can include letters, digits, underscores (_) and even single forward quotes (')
double printHi = putStrLn "Hi" --  note: not all functions take args. this one just always prints hi

double x = 2 * x --  note: where double is the NAME of the function, x is the parameter, and everything on the right side of the equals is the function body
::type double --  double :: Num a => a -> a .  note: infer what datatypes haskell believes is involved in the function. 
--  note: has format of type a goes in, a condition is applied to said type (=>) to anohter values of said type

makePercentage a b = a / b * 100
::type makePercentage -- makePercentage :: Fractional a => a -> a -> a.  note: Fractional type types come in, three fractionals are applied upon each other within
