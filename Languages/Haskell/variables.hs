{-
  This is the file variables.hs
  In this file will be examples of creating and showing basic usage of variables
  Summary: Creating: <variable_name> = <data>. Use variables anywhere you would use data. Placeholder data undefined triggers error upon actually being used
-}

-- creating variables
num = 1
num2 = undefined -- note: placeholder data.

-- using variables
show num -- use them anywhere
num `min` num
-- show num2 -- ERROR. Note: triggers error as placeholder was not redefined by sensible value. lazy evaluation demonstration
z = num + num2 -- note: whilst this is NOT evaluated (just saved as its not actual computation)
-- z  -- ERROR. note: now causes error
