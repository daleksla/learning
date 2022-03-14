{-
    This is the file exceptions.hs
    Generally, exception catching should be kept minimal. For example, if a function fails to produce a coventional answer, the Haskell approach would be to encode the output type using Maybe rather than produce an exception
    However, one may use it when dealing with the outside world, i.e. with I/O actions and other impure code

    Summary:
        * Catching errors: catch <func_to_try> <exception_handler>
        * Handler:
            * Signature: <handler_name> :: IOError -> IO ()
            * Body:
                * You can distinguish between various errors (such as isAlreadyExistsError, isDoesNotExistError, isAlreadyInUseError, isFullError, isEOFError, isIllegalOperation, isPermissionError, isUserError) and deal with each accordingly
-}

import System.Environment
import qualified Control.Exception as Exception
import qualified System.IO as IO

main = Exception.catch toTry handler -- catch function tries function, if an internal error arises, automatically calls handler

handler :: IO()
toTry = do
    (fileName:_) <- getArgs
    contents <- readFile fileName
    putStrLn $ "The file has " ++ show (length (lines contents)) ++ " lines!"

handler :: IOError -> IO ()
handler e
    | isDoesNotExistError e = putStrLn "The file doesn't exist!"
    | otherwise = ioError e
