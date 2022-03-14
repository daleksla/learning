{-
    This is the file lists.hs
    In this file will be examples of lists and related operations

    Summary:
        * lists must store items of same datatypes.

        * Creation:
            * Declaring values explicitly: [<val1>,...,<valn>]
            * Ranges: [<val1>..<valn>]
            * List comprehension: [<val> | <val> <- <list1>]

        * Access operator: <list_name> !! <idx> .

        * Operations:
            * Prepending: <element> : <list> .
            * Length: length <list>
            * Folding (HOF) a list into a single value: <foldl/foldr> <func_used_to_fold> <starting_val> <list>
                                                        OR
                                                        <foldl1/foldr1> <func_used_to_fold> <list>
                * Note: in function USED TO FOLD, first parameter to be passed list value(s) combined / computed from each fold, the second is the current element
                * Note: in foldl1 / foldr1, starting value is set as first value in provided lists
                * Note: use foldl(1), remember lists are singly linked lists so to traverse right all those times is a waste.
            * Find element: <element_to_search> `elem` <elements>
            * ADDITIONAL: https://wiki.haskell.org/How_to_work_on_lists . Module Data.List https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-List.html
-}

import qualified Data.List as DList -- note: module for additional list functionality

-- following are examples of how to create lists
myList1 = [0, 1, 2, 3]
myList2 = [0..3] -- [0,1,2,3]. note: definition of list by providing ranges of values
myList3 = [6, 8..12] -- [6,8,10,12]. note: taking into account the difference between 6 & 8, it keeps ranging up using said difference between each new number
myList4 = ['a', 'b', 'c']  -- "abc". note: remember that a list of CHAR's IS a string.
myList5 = ['a'..'y'] -- "abcdefghijklmnopqrstuvwxy". note: range for chars is alphabet. starts from A (cap A) to z (lower z)
myList6 = [1..] -- [1, ..., inf] . note: Haskell does lazy evaluation so it won't create any numbers till they're needed.
[ show x ++ show y | x <- [0,1], y <- [0,1] ] -- ["00","01","10","11"] . note: example of list comprehsnion, where a list is made using x amounts of other lists
                                                       -- in this case, we are  trying to create a list to all the  possible 4 character permutations of 0 and 1
[x | x <- [1..50], x^2 >= 25, x^3<300] -- [5, 6] . note: we can introduce conditions to the values of a given list element.

-- following are examples of list operations
head myList1 -- 0 . note: returns first single ELEMENT in its format (number)
tail myList1 -- [1,2,3] . note: returns all remaining elements (aside from head) in number list
last myList1 -- 3 . note: returns last element in list

head myList5 -- 'a' . note: returns first single ELEMENT in its format (char)
tail myList4 -- "bc" . note: returns all remaining elements (aside from head) in string / char array format
last myList4 -- 'c' . note: returns all final element in its format (char)

length myList2 -- 4
null [] -- True . note: list checks for empty values

foldl (\ total x -> total + x) 0 [1,2,3] -- 6 . note: example of foldl (left) function in Haskell. provide it with operation to perform folding, initial value, list to fold
foldl1 (\ total x -> total + x) [1,2,3] -- 6 . note: example of foldl1 function in Haskell. same as above but initial value is deduced as start of lists (1)

['a', 'b', 'c']!!1 -- 'b' . note: remember indexing starts AT 0 (not sure why one couldn't remember that at this point)

minimum myList4 -- 'a' . note: returns minimum value found in a given list
maximum myList3 -- 12 . note: returns maximum value found in a given list

['a', 'b', 'c'] ++ ['d'] -- "abcd". note: concat method.
-- note: above is also only way to append values is to wrap in list then concat. (o(n) of dst list size - not recommended)
myList1 ++ myList2 -- [0,1,2,3,0,1,2,3]

'h' : 'i' : ' ' : "i am salih" -- "hi i am salih" . note: prepend method in action. right to left (ie space added to start, then i then h). note: adds ELEMENTS (must be char in this example)

take 3 [5,4,3,2,1] -- [5,4,3] . note: returns x number of elements from beginning of list
drop 2 [1,2,3,4] -- [3,4] . note: removes number of specified elements from list (from front)
-- note: for either of these two functions, specifying you want to take MORE then the available elements causes no error. it'll just take everything

addOne elem = elem + 1 -- generic func.
map addOne [1,2,3] -- [2,3,4] . note: map is a keyword which applies a given function to a datatype. (see functions.hs for HOF)

my_test elem = elem /= 0 -- generic func.
any my_test [0,2,3] -- True . note: any returns boolean truth on whether any elements passed a given test
all my_test [0,2,3] -- False . note: all returns boolean truth on whether all elements passed a given test

4 `elem` [1,2,3,4] -- True . note: elem takes two args so its nice as infix notation style. detects whether x is an element of y

reverse [1,2,3] -- [2,3,4] . note: reverse returns a list with the order reversed

-- look online for math function such as sum, product, etc.

-- following are examples from Data.List module. See more at https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-List.html
DList.sort [8,5,3,2,1,6,4,2] -- [1,2,2,3,4,5,6,8] . note: sorts list in order providing element types are part of Ord typeclass
DList.insert 4 [3,5,1,2,8,2] -- [1,2,2,3,4,5,8] . note: inserts element between a value smaller than it and a value its smaller than. useful if the list is already sorted
DList.repeat 5 -- [5,...,5] . note: forms an infinite list containing number 5
DList.cycle [1,2,3] -- [1,2,3,1,2,3,...,1,2,3] . note: forms an infinite list of the given list looped over
