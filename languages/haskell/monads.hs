{-
    This is the file monads.hs
    In Haskell, a monad is essentially a type that wraps another type
    When would this be used? Since branches of code (functions, if/else branches) must return the same type, wrapping the value with a monad means that, so long as the monad is the same type, then it can return differing values

    Summary:

        * To extract a value from a monad: <var> <- <monad>

        * To wrap with a monad: <monad> <value>
            * Note: `return` keyword takes a pure Haskell value and puts a wrapper around it. It will *assume* the monad needs from other branches of code etc.
-}

line <- getLine -- monad extraction

if null line then return () -- due to line below, return assumes IO action monad is required. the data we gave it to wrap was just an empty tuple
else putStrLn "thanks for ur message!" -- here, an IO action is returned by putStrLn
