{-
  This is the file strings.hs
  In this file will be examples of strings and relevant operations
  Summary: String [Char] != Char . Creating: "<text>".
  ADDITIONAL: Possible string operations can be viewed in the operations section of lists.hs (strings are a shorthand char array)
-}

-- creating strings
string1 = "hello" -- "hello". note: strings are enclosed within double quotations. You may see it reported as [Char]
-- 'h' -- 'h'. note: THIS IS NOT A STRING. in Haskell this is of type 'Char'
string2 = "My long \
\string." -- \ escape allows for multiline string creation
string3 = ['a', 'b', 'c'] -- "abc" . note: a char array is a string

-- SEE lists.hs for usage examples
