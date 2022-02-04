# In R, there are two main ways to print - cat() & print()
# There is not much difference in what they do, rather it's what they return:
  # print() ~ returns what it prints as a character vector
  # cat() ~ returns a NULL object (ie. all it does is print)
# Also, while 'print()' includes a new line tag, 'cat()' does not

x = print(1 * 3)
# 3 will be printed, x will now store 3 

x = cat(1 * 3)
# 3 will be printed, x will now store NULL 