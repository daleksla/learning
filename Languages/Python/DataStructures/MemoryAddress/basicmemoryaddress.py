"""This program is an introduction to memory in python
   In python, integers, strings & essentially other primitive data types are 'immutable'
		- This means the values, once set, cannot be changed
		- However, we can change the values to which variables point to
		- This gives off the facade that we are able to change the value of a variable once set
   This program will show us how to print a variable's (current) & a value's memory address,
   		- to do this we will be using the 'id()' function """

def main():
	myInteger = 1 #create variable
	print("Original integer variable: ", id(myInteger)) #prints memory address of the data which 'myInteger' holds (ie. 1)
	print("Value 1's memory address: ", id(1)) # should print the same memory address as above (as python points to permanent data in memory)
	myInteger = 2 #change value
	print("Changed integer variable: ", id(myInteger)) #subsequently memory address printed should be different, as we are pointing elsewhere 
	print("Value 1's memory address: ", id(1)) #should still be the same as when we first printed the memory location of 1
	

if __name__ == "__main__":
	main()