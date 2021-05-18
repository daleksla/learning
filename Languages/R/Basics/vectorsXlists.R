# In R, we have two main ways of storing collections of data
  # Vectors are one-dimensional collections of values, where all data types within are the same
  # Lists are one-dimensional collections of values allowing for different types within 
	# Appears more like a dictionary / map than a list
# NOTE: index value in R starts at 1 (NOT ZERO!!!)

## Vectors ##
# Creating a Vector
people = c("salih", "saleh", "salah") #method 1 (works for all types)
sequence = seq(1,20,2) #method 2 (works for numbers)
altSequence = 1:20 #method 3 [numbers 1,2,...,19,20] (works for numbers)
# Accessing elements
print(people[1]) #prints first element of vector 'people'
cat(people[length(people)]) #calculate & index by length of vector
# Printing vectors
print(people) #prints every element of vector
# Adding vectors 
c = print(a+b) #will add each element of a + b (e.g. a[1] + b[1], a[2] + b[2], ..., etc.)

## Lists ##
# Creating a list
person = list(
	first_name = "Ada",
	job= "Programmer",
	salary = 100000,
	carparking_permit = TRUE
)
# Accessing elements:
print(person$first_name) # By name method #1
print(person[["first_name"]]) # By name method #1
# By index
print(person[1])
	