from string import *

"""Methods are functions accessed through dot notation (e.g. variable.method-name() )
   They're pretty much indistinguishable from functions, except with regards that:
   		- Methods are contained within data types; instead of just calling them directly (like functions),
		we have to first say which variable we're referring to and then call the method inside that variable.
		(So a method is a function contained inside a data structure)
		- Meanwhile typical functions are directly accessible & have been defined within our programs.
   Just like functions, they have names, parameters, some internal operation/code & may return some value(s)
   We can use methods to manipulate our variables however to do so may be too complex to be taken care of by simple operators."""

def main():
	myNumericString = "123456"
	myNonNumericString = "ABCDEF"
	name = "Salih Mahmoud Sayed Ahmed"
	otherName = "Bob Dylan"
	##
	print("myNumericString is digit?: ", myNumericString.isdigit()) 
	#boolean method, will return T/F if our string contains digits
	print("myNonNumericString is digit?: ", myNonNumericString.isdigit()) #no paramters required for some methods;
	#this is because the only data required is the variable itself
	print("name starts with 'Salih'?: ", name.startswith("Salih")) #some methods DO require arguements
	#consider it as a needed additional piece of data for the method to run
	print("otherName starts with 'Salih'?: ", otherName.startswith("Salih"))

if __name__ == "__main__":
	main()