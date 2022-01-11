{-
  This is the file booleans.hs
  In this file will be examples of boolean expressions, such as comparisons and operations
  Summary: boolean values: True, False. Comparison operators: <, <=, >, >=, ==, /=. Other boolean operators: not, ||, &&
-}

True -- True. Haskell positive boolean (1)
False -- True. Haskell negative boolean (0)

-- Following are examples of operations
False && True -- False. AND operator
True || False -- True. OR operator
not True -- False. NOT operator
-- no inherent XOR operator

-- Following are examples of numerical comparisons
456 > 123 -- True.
456 >= 456 -- True.
123 < 456 -- True.
123 <= 456 -- True.
123 == 456 -- False.
123 /= 456 -- True. Note: /= is equivalent to != (does not equal to)
5 == 5.0 -- True. despite one being int and another float types, Haskell would convert 5 to a float to give 5.0. It then compares to find that 5.0 is equal to 5.0 and not greater than 5.0.

-- comparing strings. Boolean operations are limited to comparisons for strings
"hello" == "world" -- False.
-- "a" == 'a' -- ERROR. note: again, strict type setting prevents this comparison 
"hello" /= "hello" -- True.
"abc" > "abC" -- True. orders alphabetically
"abc" >= "abC" -- True.
"abc" < "abC" -- False.
"abc" <= "abC" -- False.
