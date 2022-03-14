{-
    This is the file types.hs
    In this file will be examples of make use of types in Haskell, from defining to using

    Summary:

        * Type signatures:
            * Can query types using :t command in interpreter

        * Creating types:

            * Simplest type is called Synonym Types
                * just serves an an alias to another type (similar to typedef)
                * Syntax: type <alias> = <original>
                * makes code more legible

            * Sum types are data types which have a fixed number of existing values
                * e.g. Booleans have fixed values: True and False
                * syntax: data <type> = <val1> | ... \ <valn>

            * Tuple types, unlike sum types where there is a finite number of values, has information entering the datatype in some form of constructor
                * Therefore the type really just become a tuple of specific types
                * Syntax: data <type> = <type constructor name> <type1> ... <typeN>
                    * note: <constructor_name> doesn't have to match name of type

            * Product types essentially are a finite set of values like sum types
                * Each element is seperaed using the pipe symbol (|)
                * However, each value can also be a tuple type / constructor construct
                * Therefore it can be summised (product types) as a combination of sum and tuple types
                * Syntax: data <type_name> = <value_1> | <type constructor name> | ...

            * Record syntax stems from the fact that tuple types can become very verbose in matters such storing large quantities of data
                * Furthermore in such cases, writing getters for each of the those properties is arduous
                * Record syntax not only provides a nicer way of defining an creating objects, but automatically creates getters (each named after the field specified in the record syntax prototype)
                * Syntax: data <type_name> = <constructor_name> { <field_1> :: <type_of_field_1>, ..., <field_m> :: <type_of_field_n>}

        * Deriving type from a typeclasses:
            * A typeclass is an interface that defines some behaviour. A type can therefore be made an instances of a typeclass if it supports that behaviour
                * E.g. Int type is an instance of the Eq typeclass because it can be equated
            * We can inherit a type class by doing either of the following:
                * Manually implement derived functionality: instance <parent> <derivant> where <implementation of functionality derived>
                * Automatically generate derived functionality: `deriving (<typeclass_name1>, ..., <typeclass_name2>)` (put this at the end of a type definition)
                    * Typeclasses in which their functionalities are automatically inherited include Eq, Ord, Enum, Bounded, Show, Read

        * Creatring a typeclass:
            * Syntax: `class <typeclass_name> <made up reference to a type of instance <typeclass_name>> where <function signatures typeclass and derivatives should have> (<function bodies>)
                * where <function_bodies> is an optional addition which can be given which also then is used by other types when they become instances via automatic derivation
                * E.g. class Eq a where (==) :: a -> a -> Bool ...
            * Deriving from a typeclass is similar (sub typeclasses):
                Syntax: `class (<typeclass_name> <made up reference to a type of instance <typeclass_name>>) => <parent_type> <made up reference to a type of instance <typeclass_name>> where <function signatures typeclass and derivatives should have> (<function bodies>)`

        * Note: two main types of polymorphism in standard Haskell
            * Parametic polymorphism - where type of a given variable appears without given constraits
                * e.g. id :: a -> a contains an unconstrained type variable a in its type, and so can be used in a context requiring Char -> Char or Integer -> Integer
            * ad-hoc polymorphism - when a value is able to adopt any one of several types because it, or a value it uses, has been given a separate definition for each of those types
                * e.g. the + function essentially does something entirely different when applied to floating-point values as compared to when applied to integers
                * You can recognise the presence of ad-hoc polymorphism by looking for constrained type variables
                * e.g. elem :: (Eq a) => a -> [a] -> Bool -- a is constrained

-}

data Counter = Int -- synonym type

data Compass = North | South | East | West -- sum types

instance Show Compass where -- derive
  show North = "North!"
  show East = "East!"
  show West = "West!"
  show South = "South!"

data Point = Pt Int Int  -- tuple type
    deriving Show -- automatic string derivation method

distance :: Floating a => Point -> Point -> a -- example function using Point tuple type defined above
distance (Pt x1 y1) (Pt x2 y2) = sqrt dsqF
      where
        dx = x2 - x1
        dy = y2 - y1
        dsq = dx^2 + dy^2
        dsqF = realToFrac dsq

point1 = Pt 1 2 -- define tuple type object
point2 = Pt 2 1

data Expression = Number Int                   -- product type. tuple 1...
              | Add Expression Expression      -- ...and tuple 2...
              | Subtract Expression Expression -- ...and tuple 3
  deriving (Eq, Ord, Show)
                                               -- so what we can see is that Expression is either a number, an Add construct or a subtract construct

calculate :: Expression -> Int
calculate (Number x) = x
calculate (Add e1 e2) = (calculate e1) + (calculate e2)
calculate (Subtract e1 e2) = (calculate e1) - (calculate e2)

data Foo = Foo {x :: Integer, str :: String} -- record syntax example

fooType = Foo 1 "Hi" -- declare value of type Foo

instance Eq Foo where -- derive Foo from Eq
   (Foo x1 str1) == (Foo x2 str2) = (x1 == x2) && (str1 == str2)

fooType == Foo 1 "hi" -- compare Eq (shoudl work as == uses instances of Eq, which it clearly is)

data Person = Person { -- another record syntax example
                        firstName :: String , lastName :: String , age :: Int
                     } deriving (Eq, Show) -- automatically derive from Eq and Show

--- binary tree example type
data Tree a = EmptyTree | Node a (Tree a) (Tree a) -- define product type

singleton :: Ord a => a -> Tree a -- method creates singleton tree based on a given value
singleton x = Node x EmptyTree EmptyTree

treeInsert :: (Ord a) => a -> Tree a -> Tree a -- method insert a value in a given tree structure where A is orderable and the tree provided is a tree containing a's
treeInsert x EmptyTree = singleton x -- if empty tree type is provided, create a singleton
treeInsert x (Node a left right) -- otherwise (note: we split tree parameter into its constituent parts)
    | x == a = Node x left right
    | x < a  = Node a (treeInsert x left) right
    | x > a  = Node a left (treeInsert x right)

class (NewEq a) => Num a where -- subtypeclass derivation of Num
     (==) :: a -> a -> Bool
