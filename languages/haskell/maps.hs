{-
  This is the file maps.hs
  In this file will be examples of creating and showing basic usage of associative arrays / maps
  Summary:
    * Maps are a collection of key->value bindings
        * Note: maps are defined as a list of pairs (see tuples.hs) of strictly type a and b ( e.g. [(Num, [Char])] )
    * Creating: [ (key, val), (key, val) ]
    * Extracting: lookup <key> <dict> . Note: has function signature of lookup :: Eq a => a -> [(a, b)] -> Maybe b
        * ... where 'Maybe' is a supertypeclass datatype constructor (datatype constructor = a datatype which needs another type to properly form)
        * ... instances are 'Just' (ie associated when values are found) and 'Nothing' (ie when values are not)
        * ... b is the value associated to a given key
        * To then use the values (since Maybe pairings prevents values being used naturally), use fromJust function
            * Requires Data.Maybe module
    * Note: extended function available in Data.Map module
-}

import Data.Maybe as DMaybe

-- following is how to create a map
myDict = [ ("one", 1), ("two", 2), ("three", 3) ]

-- following is how to extract values from a map
lookup "one" myDict -- Just 1
lookup "zero" myDict -- Nothing
:info lookup -- lookup :: Eq a => a -> [(a, b)] -> Maybe b . note: Maybe is the 'parent' class of Just and Nothing, b is the datatype of the value

DMaybe.fromJust $ lookup "one" myDict -- 1 . removes weird Maybe appendage
