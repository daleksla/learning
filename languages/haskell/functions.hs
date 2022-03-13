{-
    This is the file functions.hs
    In this file contains examples of calling and writing functions
    Summary:
        * Functions are a central concept in Haskell - they are the default command / operation assumed unless an operator etc. is found appropriately
        * Two types:
            * regular functions: takes in regular data
            * high order functions: functions which either take in a function (similar to a function pointer like C), return one as output, or both
                * many built in HOFs, such as map (maps provided function call to each element in a given list)
        * Calling:
            * <function_name> arg1 ... argn .
            * Note: use brackets or the $ symbol before a given component to set precedence
        * Writing:
            * <function_name> arg1 ... argn = <func_body>
                * Function names need to be lowercase. Body of functions is singularly expression.
            * currying:
                * currying is done directly by wrapping the partial call in brackets: <func_name> = (incomplete func calls) .
                * currying indirectly is done by saving a call to a function w/o all its needed args:  <func_name> = <arg1> (no arg2 etc.).
                * The args for both types of currying can then be supplied later: <func_name> <arg2 etc.>
            * Point free function:
                * syntax:  <func_name> = (<func-name>)
                * (where arguments do not need to be explicitly stated due to assumption based on function body)
            * Lambda functions are functions not saved to a name, but can nonetheless be used like one. Syntax: (\ <arg1> <argn> -> <operation>) . Note: lambda functions are wrapped in brackets and start with a \ symbol. Each arg is seperated by a space, followed by an arrow and an operation.
            * Writing functions which returns a value based on dependant on a condition (value/pattern matching) is also common (see conditionals.hs) (theyre all conditional so THATS WHY THEYRE THERE!)
        * Function signatures:
            * Shows inputs, outputs of function e.g. <name> :: <input type> -> <output_type>, which can be read as <input_type> is mapped onto data of type <output_type>
            * Regular functions have a function signature as above
            * High order functions signature encompasses the function signature of the function it calls: applyTwice :: (a -> a) -> a -> a
-}

-- following is an example of defining a function. THEY MUST start with a lower case letter OR an underscore. They can include letters, digits, underscores (_) and even single forward quotes (')
printHi = putStrLn "Hi" --  note: not all functions take args. this one just always prints hi
double x = 2 * x --  note: where double is the NAME of the function, x is the parameter, and everything on the right side of the equals is the function body
::type double -- double :: Num a => a -> a . -- note: this provides a function signature infered by Haskell. the 'Num a =>' part says that type is instance of Num and the 'a -> a' segment says that the function takes an input of type a and returns an output of the same type

makePercentage :: Fractional a => a -> a -> a -- note: explicitly declared function signature (ie don't leave it to Haskell to infere types).
makePercentage a b = a / b * 100 -- function defined here.

isUpperAlpha :: Char -> Bool -- note: func signatures states char is needed, bool is returned
isUpperAlpha = (`elem` ['A'..'Z']) -- note: here we are partially applying the elem function. ***here currying is done directly by wrapping the partial call / function body in brackets***

add = (+) -- note: example of a point free function. When a function is defined as another function (or a composition of other functions) acting directly on the arguments, like add (just uses plus operator), we can exclude the arguments from the definition

applyTwice :: (a -> a) -> a -> a -- note: high order func. signature
applyTwice f x = f (f x)
divideByTen = (/10) -- partial function declaration
applyTwice divideByTen 123 -- pass func, number

    -- see conditionals.hs regarding how to write function 'overloads' based off conditions not within the body of the function

-- following is an example of calling functions
putStrLn "hi" --  note: parantheses are NOT required for a function call. putStrLn is the function name, "hi" is a string provided as an argument

44 `min` 33 --  note: the subtraction operator is called as an 'infix function' called min. call it as above

show (min 44 33) --  note: this example shows the output (as a string) of the result returning by 44 - 33. nested function call

x = min 44 -- note: this is an example of Currying, a technique of translating a function that takes multiple arguments into evaluating a sequence of functions, each with a single argument. this is a partial function only and would be expressed as 44-y (we still need y!).
x 33 -- 11. note: here we give it the y component, fulfilling the expression.
-- note:

(+) 1 5 -- 6 . note: calling infix add operator. wrapping brackets allows for a partial applied function call, which we then supply the args for straight after

map (+3) [1,2,3,4,5]  -- [4,5,6,7,8] . note: 'map' is a high order function, whioch takes in a function call
filter (>3) [1,5,3,2,1,6,4,3,2,1]  -- [5,6] . note: 'filter' in a HOF which takes in partial function call too
filter (\ str -> if ((length str) `mod` 2) == 0 then True else = False) ["one", "four"] -- ["four"] ~ filters out strings of an odd length (keeps even length'd) . note: demonstrates example of lambda function.
                                                                                        -- lambda functions are wrapped in brackets and start with a \ (looks like lambda symbol). Then, each arg is seperated by a space, followed by an arrow and an operation.

(*) 2 $ 2 + 1 -- 6 . note: this dollar function is a weird way instead of using brackets - gives the right side of the operation precendence
