{-
    This is the file glueing_actions.hs
    Haskell permits only one line per function. However there are cases, such as if you were to request input and make an output based on such a computation in the main function, which require multiple lines of code
    Ideally, these kind of glueings are only really done when IO is involved because its a necessity. It is bad practise therefore to do it simply to enforce a procedural programming perspective
    SUMMARY:
        * Glueing multiple statements together (do block): <func_name> = do
                                                                <line1>
                                                                ...
                                                                <linen<
            * Note: any form of relative indentation is REQUIRED
        * Executing a series of steps (sequence command): sequence [<func1> <param1..n_if_needed>>, ..., <funcn>]
            * Note: data returned by this will need to be extracted (same way as shown in monad.hs)
-}

-- NOTE: The main function always has a type signature of main :: IO <something> (see io.hs)

main = do -- do command glues the four statements below into one action
    a <- getLine
    b <- getLine
    c <- getLine
    print [a,b,c]

main = do
    rs <- sequence [getLine, getLine, getLine] -- data
    print rs
