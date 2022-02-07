{-
    This is the file randomness.hs
    In Haskell, (pseudo) random number generation still requires a functional programming approach. Note: all functionality found in System.Random.
    Summary:
        * Creating random number generator:
            * Manually creating random number generator: mkStdGen <seed>
            * Using system: getStdGen
                * Note: this returns IO action. Extract generator using `<-` (see monads.hs, io.hs)
                * Can therefore only run in main
            * NOTE: calling a random function using these generators will always give you the same result. It would be best if one were to write a program reading from /dev/urandom (for example) and use such a value for seeding
        * Generating random number:
            * Single number: (<rand_num>, <num_representation_of_num_generator>) = random <rand_num_generator> / randomR <tuple_range> <rand_num_generator>
                * Returns both a random number and a new random number 'generator' (in text form)
                * When next using random number generator, use the new random geenrator returned from the above rather then reseeding to create another one from scratch
            * Multiple: randoms <rand_num_generator> / randomsR <tuple_range> <rand_num_generator>
                * Returns infinite list of random numbers
-}

import qualified System.Random as Rand
import Data.Maybe as DMaybe

Rand.random $ Rand.getStdGen

Rand.random (Rand.mkStdGen 1) :: (Float, StdGen) -- note: we can request beyond random integers. here we cast the tuple of the random generator to give us floats as the first value in the pair

take 5 $ Rand.randomsR (1,6) (Rand.mkStdGen 10)

-- example real life usage

module RandModule (randomElement, randomCutList, randomisedList) where
  import qualified System.Random as Rand
  import qualified Data.Maybe as DMaybe
  import qualified Data.List as DList

  _CaculatedFixedIndex :: Eq a => [a] -> Int
  _CaculatedFixedIndex list = fst $ Rand.randomR (0, (length list) - 1) (Rand.mkStdGen (length list))

  _IndexedDelete :: Eq a => Int -> [a] -> [a]
  _IndexedDelete i list = take i list ++ drop (1 + i) list

  randomElement :: Eq a => [a] -> DMaybe.Maybe a
  randomElement [] = DMaybe.Nothing
  randomElement list = DMaybe.Just $ list !! (RandModule._CaculatedFixedIndex list)
