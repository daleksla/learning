{-
  This is the file strings.hs
  In this file will be examples of strings and relevant operations

  Summary:

    * Creating: "<text>".

    * String [Char] != Char .

    * Operations: Possible string operations can be viewed in the operations section of lists.hs (strings are a shorthand char array). More functions available in Data.Char (at least for a strings individual characters) https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-Char.html
-}

import qualified Data.Char as DChar

-- creating strings
string1 = "hello" -- "hello". note: strings are enclosed within double quotations. You may see it reported as [Char]
-- 'h' -- 'h'. note: THIS IS NOT A STRING. in Haskell this is of type 'Char'
string2 = "My long \
\string." -- \ escape allows for multiline string creation
string3 = ['a', 'b', 'c'] -- "abc" . note: a char array is a string

-- SEE lists.hs for usage examples

-- following are examples from Data.Char module. THERE ARE MANY MORE - see https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-Char.html
all DChar.isSpace "salih" -- False. note: checks whether all the characters in the string are white-space characters (including spaces, tab characters, newlines, etc.)
any DChar.isLower "Salih" -- True. note: checks whether any character within the string is lower-cased.
DChar.isUpper (head "Salih") -- True. Note: checks whether the first letter of a string is upper-cased.
DChar.isDigit (tail "1234") -- True. note: checks whether the last character is a digit.
DChar.generalCategory '.' -- note: function can classify characters
(DChar.toUpper (head "salih")) : "alih" -- "Salih" . note: toUpper gets character and uppercases it, then its prepended to the string "alih"
