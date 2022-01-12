{-
    This is the file lists.hs
    In this file will be examples of lists and related operations
    Summary: lists must store items of same datatypes. Creation: [<val1>,...,<valn>] . Access operator: <list_name> !! <idx> . Prepending: <element> : <list> .
    ADDITIONAL: https://wiki.haskell.org/How_to_work_on_lists
-}

-- following are examples of how to create lists
myList1 = [0, 1, 2, 3]
myList2 = [0..3] -- [0,1,2,3]. note: definition of list by providing ranges of values
myList3 = [6, 8..12] -- [6,8,10,12]. note: taking into account the difference between 6 & 8, it keeps ranging up using said difference between each new number
myList4 = ['a', 'b', 'c']  -- "abc". note: remember that a list of CHAR's IS a string.
myList5 = ['a'..'y'] -- "abcdefghijklmnopqrstuvwxy". note: range for chars is alphabet. starts from A (cap A) to z (lower z)

-- following are examples of list operations
head myList1 -- 0 . note: returns first single ELEMENT in its format (number)
tail myList1 -- [1,2,3] . note: returns all remaining elements (aside from head) in number list
last myList1 -- 3 . note: returns last element in list

head myList5 -- 'a' . note: returns first single ELEMENT in its format (char)
tail myList4 -- "bc" . note: returns all remaining elements (aside from head) in string / char array format
last myList4 -- 'c' . note: returns all final element in its format (char)

length myList2 -- 4
null [] -- True . note: list checks for empty values

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
map addOne [1,2,3] -- [2,3,4] . note: map is a keyword which applies a transformation to a datatype. in Haskell, a list makes it apply changes to every element. kinda like a loop?

my_test elem = elem /= 0 -- generic func.
any my_test [0,2,3] -- True . note: any returns boolean truth on whether any elements passed a given test
all my_test [0,2,3] -- False . note: all returns boolean truth on whether all elements passed a given test 

4 `elem` [1,2,3,4] -- True . note: elem takes two args so its nice as infix notation style. detects whether x is an element of y

reverse [1,2,3] -- [2,3,4] . note: reverse returns a list with the order reversed

-- look online for math function such as sum, product, etc.
