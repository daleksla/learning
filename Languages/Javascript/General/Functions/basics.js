/* In JavaScript, as in most other languages, code can be divided in to modular blocks called functions
	 * Once defined, these can be called from other areas of code
 * This allows us to re-use blocks of code, especially common ones
 * These blocks of code will  have their own scopes & therefore their own variables etc., inaccessible to procedures outside of it 
 * Functions may require data to be passed (in the form of parameters)
 * Functions may also return data to where it was called from 
 * What happens if we only supply a single argument?
 * If an argument is not supplied for a parameter it is assigned a value of `undefined`
	 * An undefined variable is one that has been declared but has not been assigned a _value_ 
 * Function's in Javascript DO NOT support overloading - it will only use the last version of that function defined 
	 * Therefore, to mimic overloading with varying numbers of parameters, we need to use 'rest parameters'
		 * These allow us to represent an indefinite number of arguements as an array
		 * To do this, when defining the function, we preceed the parameter name with three dots ('...') */

function printName() // no parameters
{
  let name = 'John Doe'
  console.log(`Hello ${name}`) //this function will print Hello John Doe
}

function counter()
{
	for(let i = 0 ; i < 10 ; i++)
	{
		console.log(i)
	}
}

printName() //this will call the function
counter()

// console.log(`Hello ${name}`) //this will not run, as the name variable is only within the printName()'s scope

function largestNumber(a, b) //two parameters (a,b)
{
	if(a > b)
	{
		return a
	}
	else if(b > a)
	{
		return b
	}
	else {
		return null //intentionally returns nothing
		//note: it will return nothing regardless if it reaches the end of the function
	}
}

//here, we directly print the return value of the function
console.log(`the biggest number is: ${largestNumber(5, 8)}`)

//or, we could save the value
let largestValue = largestNumber(5, 8)

function add(...numbers) //here we use rest parameters to mimic overloading with untold numbers of variables
{
  let total = 0
  for(let num of numbers) 
   {
    total += num
  }
  console.log(typeof numbers) //this will print the numbers variable as 'array'
  return total
}