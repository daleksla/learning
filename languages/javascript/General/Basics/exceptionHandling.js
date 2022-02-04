/* Some errors can occur which will cause the code to crash
 * Whilst it is important to write your code carefully there will always be errors
 * To manage these you will need to add some exception handling
	 * This wraps around code that may throw an error and includes a block of code to run if an error occurs 
	 * This is done by enclosing your code in a 'try' statement
	 * The 'catch' statement is ran if something fails / an error is thrown in latter 
 * You use exception handling for built-in errors but you can also throw you own 
	 * To do so, use either the 'throw' or 'throw new error' option
		 * Using the throw option means that the error message passed in the brackets will become the caught error itself
		 * Using the throw new object means the object will have the 3 attributes as previously mentioned - in the brackets will be the 'message' attributes */

try {
  // The lines of code that might throw an exception
  let dividend = 2
  let divisor = 0
  if(dividend === 0)
  {
	  throw new Error('trying to divide zero') //this will by default overwrite the err object
  }
  else if(divisor === 0) 
  {
	  throw new Error('dividing by zero') //this creates a unique error, called Error
  }
  let quotient = dividend / divisor
  console.log(`${dividend}/${divisor}=${quotient}`)
} 
catch(Error) { //parameter is a reference to the error - it contains three attributes - name(internal error name), message(description of error), stack(where the error was thrown from)
  // This code runs if an exception is thrown
  console.error(Error.message)
	//this will be triggered regardless if it's a natural error or it's one we throw ourselves
	//NOTE: if you throw an error of ur own, u must print the error object itself, as it'll have no attributes
}
finally {
  // This code runs whether there's been an exception or if the code ran successfully
  console.log('lets tidy things up')
}