/* As said previously - Javascript is a loosely typed languages (determines datatypes of variables as it goes along)
 * This program will explore the datatypes Javascript using the 'typeof' keyword
	 * e.g. console.log(typeof insert-data-variable)
 * Note: we can print the datatype of a variable / value by 
	 * String - a sequence of character enclosed in quotes
		 * There are three types of quotes we can use: 
			 * single ('') [normal]
			 * double ("") [not recommened]
			 * backticks (``) [extended functionality quotes]
				 * string interpolation (printing a string (message) along with a variable) only works if the string is enclosed using the backtick character
	 * Numbers - any numerical / numeric-esque value not enclosed in quotes
		 * Note: in JavaScript both integers and floating point numbers are considered the same type
		 * The result of any mathematical operation will produce a value of type number
			 * Note: If you attempt to perform a mathematical operation on a non-number / non-numberesque value, it shall print 'NaN' (not a number)
	 * Boolean - a boolean variable can contain one of two values, (true or false)
		 * as in other languages, this is used to flag a yes/no option
*/

//below are strings

let name = 'John Doe'
console.log(name)
console.log(typeof name)

let adams = "42"
console.log(adams) 
console.log(typeof adams) //this will print string also, as it is enclosed in quotation marks also

console.log(`my name is ${name}.`) //this is called 'string interpolation' - it will print a message along with the value stored in the variable

//below are numbers

let pi = 3.1415
console.log(pi)
let a = 42 / 0 //this will print infinity
console.log(a)
let b = "42" / 2 //this will convert the value 42, despite being a string, into a number and divide it
console.log(b)
let c = "forty two" / 2 //this will cause an error
console.log(c)