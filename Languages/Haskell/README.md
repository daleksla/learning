# Haskell

Haskell is a language centered around the 'functional programming' paradigm - nearly all functions are 'pure functions' (ie functionality MUST run with the same output given the same input, no alterations to the state of it's host).

As with many programming languages, it is organised modularly, but the concept of pure functions allows us to view and test each function independently without worrying about the rest of the program having issues with it etc.

It also has other features, such as:
* Lazy evaluation - the method which Haskell uses to run it's expressions, such as they are not evaluated when, for example, they are bound to variables, but later such as when their results are needed by other computations
* Statically typed, strongly typed - Haskell enforces a type system (ie it is aware of what data-types a variable should have), which allows for fast debugging. Unlike other interpreter and compiler software, Haskell is very good at determining the inherent data-types of values, reducing the verbose aspect of such a system, but they can be specified (which may reduce scope of possible operations in the long run)
  > Note: It is nonetheless standard practice to at least give a signature for your top level functions and objects
* Compiled or interpreted - Haskell is able to run code it in it's native interpreter or can compile code into an optimised binary
* Concurrency - Haskell has many libraries to make parallelising code easier
* Metaprogramming - tools to support the generation of a programs syntax tree
* Ecosystem - Haskell is a well known and supported language, with many additional resources available
  * Hackage - repository containing over 14000 open-source packages
  * Stackage - collection of over 2000 packages guaranteeing compatibility with each other
  * Hoogle - resource search engine to find relevant packages

As with other programming languages, features such as variables, functions, modules, exceptions, I/O, data type creation etc. are available. Note that loops are absent (as loops encourage side effects and mutable states!).

***

To get started with Haskell:
Note that `stack` is the main Haskell command (think of it as `python3`)
* Open interactive interpreter - `stack gchi`
  * simply then type in desired command such as `putStrLn "Hello World"`
  * Note: you can then import libraries / scripts written using `:l <filename>.hs`. If any changes are made to the source code when the interpretter is open, typing `:r` will update all changes
* Compile code ONLY - `stack gch <filename>.hs` (note: file must contain a function named 'main')
  * This produces a binary file of the same name in calling directory
  * Example of compilable code: ```main = putStrLn "Hello World"```
  * To then run the code: `./<filename>`
* To compile a given file and run it (note that compiled output won't be saved like latter command): `stack runhaskell <filename>.hs`
