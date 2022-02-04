{-
    This is the file io.hs
    Haskell is a purely functional language. One of the requirements is that functions cannot change some external state of the program - doing this is called a side-effect of a function. However I/O is available, though it is executed differently then regular haskell functionality
    Summary:
        * IO Functions in haskell return an I/O action type constructor (i.e. it requires another type to come with it to properly form)
            * These bindings do not return associated values themselves. Rather, they return computer code that if executed would produce these things (as well as perhaps doing other side effects such as printing to the terminal)
            * I/O Action can only be run in the main function (or in GHCi as each line in GHCi is like its own main function)
                * The main function always has a type signature of main :: IO <something> but the convention is not to hard code in the type signature for main.
                * BUT REMEMBER, HASKELL CAN ONLY HAVE ONE LINE PER FUNCTION. HOW DO WE RUN MORE THEN ONE??? If we want to perform multiple I/O Actions in our program (e.g. receive input and print) then we need to glue these into a single I/O Action using a 'do' block.
                * To bind to / extract the output of an I/O Action we have to use <- (e.g. x <- getLine)
                    * Note: You are not allowed to extract the final IO action in the final line of a do block - as that is what the compiler takes as the result of the entire do.
        * Printing: putStrLn <strings>
                    print <types_convertible_to_strings>
            * Type signature: `putStrLn :: String -> IO ()`. IO action returned is bound with an empty tuple
        * Input: <var> <- getLine
            * Note: awaits new-line terminated string
            * Type signature: `getLine :: IO String`. IO action returned is bound with the inputted string

-}

main = do
    -- following are examples of how to print
    putStrLn "Hello World!" -- (prints) Hello World . note: prints strings only!
    putStrLn $ show 1 -- (prints) 1 . note: show converts instances of 'Show' typeclass to strings
    print 1 -- (prints) 1 . does the line above implicitly
    -- following are examples of how to read in values
    x <- getLine -- note: awaits new-line terminated stringYou are not allowed to extract the final IO action in the final line of a do block - as that is what the compiler takes as the result of the entire do.

main = do
    putStrLn "How old are you?"
    age <- getLine -- extract values
    let numAge = read age :: Int -- cast str using read, use 'let' to save scoped variables / bindings as you would do in a single expression (see variables.hs)
    let numDays = numAge * 365
    putStrLn $ (show numDays) ++ " days"
