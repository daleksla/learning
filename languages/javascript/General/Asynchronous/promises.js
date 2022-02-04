/* Promises are used to handle asynchronous operations in JavaScript
 * They are easy to manage when dealing with multiple asynchronous operations where callbacks can create callback hell (leading to unmanageable code)
 * Benefits of Promises
	* Improves Code Readability
	* Better handling of asynchronous operations
	* Better flow of control definition in asynchronous logic
	* Better Error Handling
 * A promise is an object that may produce a value some time in the future, which will be one of three states:
	 * Pending – the promise has not finished running
	 * Resolved – the promise has finished running and has produced some data
	 * Rejected – there was a problem carrying out the task and the promise is flagging the error
 * Promises essentially wrap a callback
	 * The Promise constructor takes only one argument (a callback function)
	 * The Callback function parameter should have two attributes - resolve, reject
	 * It will call either parameter 
 * Promises have some limitations:
	 * You can’t include conditionals (if statements etc.) in promise chains
	 * Each part of the chain can only have one parameter
	 * The error handling is significantly different from the usual try-catch */

var promise = new Promise( (resolve, reject) => { //here we create a callback, make it a promise, and then store it into a variable
  const x = "geeksforgeeks"; 
  const y = "geeksforgeeks"
  if(x === y) { 
    resolve(); 
  } else { 
    reject(); 
  } 
}); 

function success() {
	console.log('Success, You are a GEEK'); 
}

function failure() {
	console.log('Some error has occured'); 
}
  
console.log('hello')
promise.then(success).catch(failure); //this will print last, it's a seperate function
//call both methods, only the appropriate one will be run
console.log('bye')