/* To print to the console using JS, we use the console.log() function 
	 * To print a variable by itself, we simply type the variable name within the brackets
	 * However, to print a message & a variable, we use the following structure:
		 * console.log(`insert-message ${var-name}`) 
 * To print a message as a system dialog, use the alert() function
	 * It works the same as console.log() regarding printing directly, variables & both alongside each other
 * Note: The purpose of 'use strict' is to indicate that the code should be executed in "strict mode".
	 * With strict mode, you can not, for example, use undeclared variables
	 * To use this mode, place it at the start of the file */

'use strict'

console.log("Hi") //prints Hi string
var greeting = "Hi" //stores Hi string in variable called greeting
console.log(greeting) //prints greeting variable
console.log(`my name is ${greeting}.`) //this is called 'string interpolation' - it will print a message along with the value stored in the variable
console.log(5) //prints value 5
alert('Salih')