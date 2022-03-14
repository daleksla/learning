{-
  This is the file tuples.hs
  In this file will be examples of creating and showing basic usage of tuple containers

  Summary:

    * Tuple are stored to pass and return multiple bits of data. Unlike lists, they can store different data types
        * Note: tuples are defined by the types they hold and THE LENGTH
        * Note: a tuple with two elements sn commonly used and is thus referred to as a 'pair'

    * Creating:
        * From scratch: (<elem_1>, ..., <elem_n>)
        * 'Zipping' combines two lists by joining elements with the same index from the respective lists and creating a list of resultant tuples: zip <list_1> <list_2>

    * Extracting:
        * Getting first element: Prelude.fst <tuple>
        * Getting second element: Prelude.snd <tuple>
        * Note: fst and snd only work on pairs
-}

-- following is how to create a tuple
x = (1,2,"salih")
::type x -- x :: (Num a, Num b) => (a, b, [Char]) . note: look at the last bracket specifically noting the types within
y = (1,2) -- creation of a pair, the most commonly used tuple
zip [1 .. 5] ["one", "two", "three", "four", "five"] -- [(1, "one"), (2, "two"), (3, "three"), (4, "four"), (5, "five")]

-- following is how to extract values from a tuple
fst ("one", "two") -- "one" . note: takes first element only
snd ("one", "two") -- "two" . note: takes latter element from tuple
