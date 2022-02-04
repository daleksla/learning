"""This program will look at how differently memory address' are used based on mutability
   The type assigned to the variable name dictates which way Python should operate
   We will create two variable's holding the same value and we'll do the same with lists 
   We'll then do a boolean comparison on their address' 
   Python declares that if data is of a mutable type, it should always create that value in a new place in memory
		- This is unlike immutable data types, which allows for multiple variables to point to a single place"""

def main():
	myInteger = 1 #create variable
	myOtherInteger = 1 #create variable holding the same value
	print("myInteger's memory address: ", id(myInteger))
	print("myOtherInteger's memory address: ", id(myOtherInteger))
	print("Are they the same memory address?: ", (id(myInteger) == id(myOtherInteger))) 
	#should be true, as they point to an unchangeable spot in memory
	myList = [1,2,3]
	myOtherList = [1,2,3]
	print("myInteger's memory address: ", id(myList)) 
	print("myOtherInteger's memory address: ", id(myOtherList)) #different from the above
	print("Are they the same memory address?: ", (id(myList) == id(myOtherList))) 
	#false- lists are a mutable data type; python based on that to store the lists seperately in their own space

if __name__ == "__main__":
	main()