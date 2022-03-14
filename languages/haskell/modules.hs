{-
    This is the file modules.hs
    In this file will be examples of declaring, importing and making use of modules in Haskell

    Summary:

        * Importing:
            * Importing into global namespace: import <module_name> .
            * Importing module as contained namespace: import qualified <module_name> .

        * Creating:
            * To create a module: module <moduleName>( <exported_functions> ) where <all function definitions> .
            * Save the module in a file called <moduleName>.hs
-}

-- Following are examples of import module contents
import Data.List hiding (nub) -- import module involving list functionality EXCEPT nub function. Note: all imports MUST be declared at top of file
                 -- this import statement brings code into GLOBAL namespace.

import Data.List (nub) -- import specified functionality from specific module

import qualified Data.Map as DMap -- import module as contained namespace. set package name from Data.Map -> DMap.
                                  -- this helps avoid clashes

-- Following is an example of creating your own module. NOTE: needs to be contained in seperate file with the same name .hs
module Salih (printSalih, printYusuf, printMusa, printPeem) where
    print str = str
    printSalih = Salih.print "salih"
    printYusuf = Salih.print "yusuf"
    printMusa = Salih.print "musa"
    printPeem = Salih.print "Peem"
