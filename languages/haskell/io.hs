{-
    This is the file io.hs (see monads.hs first)
    Haskell is a purely functional language. One of the requirements is that functions cannot change some external state of the program - doing this is called a side-effect of a function. However I/O is available, though it is executed differently then regular haskell functionality
    IO Functions in haskell return an I/O action type constructor  (i.e. it requires another type to come with it to properly form) as well as items of data
    Both these form a monad (see monad.hs) of both computer code that if executed would produce these things (as well as perhaps doing other side effects such as printing to the terminal) and a value
    I/O Action can only be run in the main function (or in GHCi as each line in GHCi is like its own main function)
        The main function always has a type signature of main :: IO <something> but the convention is not to hard code in the type signature for main.
        Therefore you are not allowed to extract the final IO action in the final line of a do block (ie must remain in the weird IO action) - as that is what the compiler takes as the result of the entire do.
    Summary:
        * Opening a file:
            * openFile "<fileName>.txt" <mode>
                * Note: mode can be ReadMode, WriteMode, AppendMode, ReadWriteMode
        * Closing a file:
            * hClose <fileHandle>
        * Printing/Writing: putStrLn <strings> / hPutStr <handle> <strings>
                    print <types_convertible_to_strings> / hPrint <handle> <types_convertible_to_strings>
                    writeFile <path of file> <text_content>
                    appendFile <path of file> <text_content>
            * Type signature: `putStrLn :: String -> IO ()`. IO action returned is bound with an empty tuple
        * Input:
            * readFile <file_path_to_read_from>
            * getLine / hGetLine <fileHandle>
                * Note: awaits new-line terminated string
                * Type signature: `getLine :: IO String`. IO action returned is bound with the inputted string (see monad.hs for how to extract from a monad)
            * getContents / hGetContents <fileHandle>
                * Note: reads from stdin / declared file stream till it encounters an EOF
                * Unlike other IO functions, this is explicitly lazy. even in a do block, this will only extract data when it is explicitly needed
                    * Rather it assigns the promise of a string
            * interact <function_name_to_run_on_input_data>
                * This is a useful shortcut way of reading in values from stdin, performing a function call on it, and printing the value all on the same line (to stdout)
                * Removes need to use do block
            * Command line arguments: getArgs
                * Note: uses System.Environment library
        * Note: h<ioFunction> variants are found in the System.IO module (https://hackage.haskell.org/package/base-4.16.0.0/docs/System-IO.html#v:hPutStrLn)
-}

import qualified System.IO as IO

main = do -- notice its in a do block
    -- following are examples of how to print
        putStrLn "Hello World!" -- (prints) Hello World . note: prints strings only!
        putStrLn $ show 1 -- (prints) 1 . note: show converts instances of 'Show' typeclass to strings
        print 1 -- (prints) 1 . does the line above implicitly
    -- following are examples of how to input
        putStrLn "How old are you?"
        age <- getLine -- extract values
        let numAge = read age :: Int -- cast str using read to int, use 'let' to save scoped variables / bindings as you would do in a single expression (see variables.hs)
        let numDays = numAge * 365
        putStrLn $ (show numDays) ++ " days"
    -- following are examples of how to do some of the above BUT with specific files
        inHandle <- IO.openFile "/dev/stdin" IO.ReadMode
        contents <- IO.hGetLine inHandle
        IO.hClose inHandle
        outHandle <- IO.openFile "/dev/stderr" IO.WriteMode
        IO.hPutStrLn outHandle contents
        IO.hClose outHandle
        writeFile "/dev/stdout" "hi!"
