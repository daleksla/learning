"""As previously discussed, most primitive data types are 'immutable'
		- This means the values, once set, cannot be changed
   Mutable data types however CAN be changed (ie. the value within the memory address is modified)
   This program will show us the result a variable's memory address (immutable) AND a list's (mutable)
   		- again we will be using the 'id()' function
   Note: changing the mutable data type to it's original value after WILL NOT give it it's old memory address"""

def main():
	myInteger = 1 #create variable
	print("myInteger memory address (o.g.): ", id(myInteger)) #prints memory address of the data which 'myInteger' holds (ie. 1)
	myInteger = 2 #change value
	print("myInteger memory address (changed): ", id(myInteger)) #subsequently memory address printed should be different, as we are pointing elsewhere 
	###
	myList = [1,2,3] #create list
	print("myList (o.g.): ", id(myList)) #prints memory address of list
	myList.append(4) #modifies list
	print("myList (appended): ", id(myList)) #this memory address SHOULD be the same as the previously displayed one as it's mutable
	myList = [5,6,7,8] #completely overwriting list
	print("myList (overwritten): ", id(myList)) #prints new memory address, as we've essentially changed what myList is storing entirely

if __name__ == "__main__":
	main()