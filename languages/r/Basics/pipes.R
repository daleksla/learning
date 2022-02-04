# Pipes are used to take output of one function and provide it as thye first argument to the next
# This is an alternative to nested function calls or saving one-off values in variables 

# The following line of code prints 'Salih' twice
print("Salih") %>% print() # the first print output but also returns its data, which gets passed through the pipe to the print function
# this secondary function takes the first's output, thus printing 'Salih' again
