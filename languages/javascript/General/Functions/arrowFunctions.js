/* Functions may be stored in variables
 * These are used so frequently in JavaScript that a simplfied syntax, known as Arrow Functions, was made
 * The only difference is the removal of the function keyword and the addition of a fat arrow symbol => between the parameters and the body of the function
 * To further simply the syntax of arrow functions:
	 * if the function only has one parameter, we do not need to put brackets around it
	 * if the function has only one line of code, the curly brackets do not need to enclose it
	 * if the curly brackets are removed and there is a return value, the return keyword is no longer required (ie. just put the line of code) */

function returnName(name)
{
	return `hi ${name}`
}

//original function
let hello = function(name) 
{
  return `hi ${name}`
}

//just the arrow
let hello = (name) =>
{
  return `hi ${name}`
}

//removal of brackets and non-needed braces
let hello = name => return `hi ${name}`

//removal of non-needed return
let hello = name => `hi ${name}`