/* In JavaScript, functions are a data type (like strings and numbers) that can be assigned to variables
 * Because we are assigning the function to a variable we don’t give it a name directly
	 * This is known as defining an anonymous function, using the function keyword in place of the function name
	 * Anonymous functions are used heavily in JavaScript */

hello = function(name) 
{
  console.log(`hi ${name}`)
}

hello('John') //to call the function, simply use the variable name and parameter names if needed

const sum = function(...numbers)
{
	let total = 0
	for(const num of numbers)
	{
		total += num
	}
	return total
}

console.log(sum(1,2,3,4,5))