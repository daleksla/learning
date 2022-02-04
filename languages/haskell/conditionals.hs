{-
    This is the file conditionals.hs
    In this file contains examples of writing conditional statements (if statements, case statements)
    Summary:
        * Creating:
            * If statements:
                * Singular ifs: if <condition> then <true_branch> else <false_branch>
                * Nested ifs: if <condition> then <true_branch> else (if <nested_condition> then <nested_true> else <nested_false>)
                * Note: there are no else if statements, so nested statements is how to achieve something similar
            * Case Expressions:
                * Creating: case <variable> of <case1> -> <branch1>
                                               <caseN> -> <branchN>
            * Value/Pattern matching:
                * Can be made by declaring multiple versions of a FUNCTION, where the parameters are explicitly declared to match a specific value or condition
                * If defining by a specific value / pattern: <func_name> <specified_val/pattern> = ...
                                                             ...
                                                             <func_name> <param_name> = ... -- serves as generic case
                * If a conditional operation is required to ascertain the value to return: <func_name> <param> 
                                                                                               | <condition> = ...
                                                                                               ...
                                                                                               | otherwise = ... -- generic case
                    * Note: where clause can be put under all these conditions to calculate the value once, store that result in a variable / name and use it within the above conditions
        * Using:
            * You can store as a variable as usual: var = <if statement>
            * You can directly use the if statement as part of an expression: (<if statement>) + 1
        * If expressions are not better supported in Haskell is that they are rarely used
-}

-- following are examples of creating if statements
printStrange x = if length x == 0 then putStrLn "hi" else putStrLn x -- note: else case is always mandatory. similar to mathematical functions, all computations should provide an answer]
numberSizer = if x < 10 then "small" else (if x > 100 then "big" else "medium")

case n of 1 -> "one" 2 -> "two" 3 -> "three"

-- following are examples of creating (switch) case statements
digitToWord n = case n of 1 -> "one" -- standard switch case statement
                        2 -> "two"
                        3 -> "three"

-- following are examples of forms of pattern matching
describeList xs =   case xs of []    -> "empty." -- Example of case expression-based pattern matching. we are looking at the type of the value (ie the contents of xs etc.)
                               [x]   -> "a singleton."
                               [x,y] -> "a pair."
                               xs    -> "too darn long." -- essentially the else clause (ie. whatever the variable is)
-- Note that xs is a traditional variable name for a list in Haskell, while x is the traditional name for a single element from a list. the list MUST be called xs to do this

myHead someList = case someList of [] -> undefined
                                   (x:_) -> x -- if list aint undefined, split into x, the rest into _ (ie xs does not get saved, discrad it with _)

-- following are examples are forms of function based overloading for value / pattern matching
sayMe :: (Integral a) => a -> String -- function based pattern matching header
sayMe 1 = "One!" -- explicit overload when one is specified
sayMe 2 = "Two!" -- etc.
sayMe 3 = "Three!" -- etc.
sayMe x = "Too Big" -- generic case

mySum :: (Num p) => [p] -> p
mySum [] = 0 -- if list provided was empty, always return 0
mySum all@(x:xs) = x + mySum (tail all) -- generic case
-- Note that we can use the @ symbol to break a sequence into a pattern and still have a reference if needed to the whole sequence (e.g.: capital all@(x:xs) = "The first letter of " ++ all ++ " is " ++ [x])

quicksort :: (Ord a) => [a] -> [a]
quicksort [] = [] -- base case pattern . note: takes in an empty list
quicksort (x:xs) = (quicksort [a | a <- xs, a <= x])  ++ [x] ++ (quicksort [a | a <- xs,  a > x]) -- regular case where an input function exists

degreeClass :: (Num a, Ord a) => a -> String
degreeClass score  -- note: instead of explicitly declaring the values, we can still use boolean expressions to express the overloads. Needs to be written only in this format (ie not seperate function declarations etc like pattern / specific value matching)
    | score >= 70 = "First Class"
    | score >= 60 = "Upper Second"
    | score >= 50 = "Lower Second"
    | score >= 40 = "Third"
    | otherwise = "Fail" -- else, generic overload

classification listOfGrades -- same as above BUT input is list and need a value to be calculated
    | av >= 70 = "First Class"
    | av >= 60 = "Upper Second"
    | av >= 50 = "Lower Second"
    | av >= 40 = "Third"
    | otherwise = "Fail"
    where -- where clause can be appended to a function return expression to provide name bindings that will hold only in the scope of that expression. must be indented to function header
         av = (sum listOfGrades) / (length listOfGrades) -- here we can create a variable rather than compute the value within each clause



