/* Due to the limitations associated with promises, async functions werre developed as an alternate syntax
 * The changes to the syntax allow you to create promise chains by writing code that’s as easy to read and debug as standard synchronous code
 * It simply allows us to write promise-like code as if it was synchronous and it checks that we are not breaking the execution thread
 * Async functions will always return a value
	 * It makes sure that a promise is returned
	 * If it is not returned then javascript automatically wraps it in a promise which is resolved with its value 
 * The await operator is used to wait for a Promise
	 * It can only be used inside an async function*/

async function printName(name) {
	let promise = new Promise( (resolve, reject) => { //here we create a callback, make it a promise, and then store it into a variable
	  const x = "geeksforgeeks"; 
	  const y = "geeksforgeeks"
	  if(x === y) { 
		resolve(); 
	  } else { 
		reject(); 
	  } 
	}); 
	try { 
		console.log(name)
	}
	catch(err)
	{
		console.log(err)
	}
}

console.log('Hi')
printName('Enoch') //threads off here (as it's asynchronous function)
console.log('Bye')