{-
  This is the file strings.hs
  In this file will be examples of strings and relevant operations
  Summary: Creating: "<text>". Concatenating: "<text>" ++ "<text>"
-}

-- creating strings
"hello" -- "hello". note: strings are enclosed within double quotations. You may see it reported as [Char]
-- 'h' -- 'h'. note: THIS IS NOT A STRING. in Haskell this is of type 'Char'
string1 = "My long \
\string." -- \ escape allows for multiline string creation

-- cocatenating strings
"hello" ++ " " ++ "world" -- "hello world". note: three-string cocatenating operation, uses ++ operator between with each string
-- "hello" ++ ' ' ++ "world" -- ERROR. note: this does not work as ++ cannot concatenate Char objects, only [Char]
