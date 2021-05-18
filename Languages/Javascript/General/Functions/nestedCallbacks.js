/* Due to the fact that the code you execute after a callback (ie how you deal with the data or an error) is inside the callback code, it can be be a challenge to write a script
 * Callback hell is any code where the use of function callbacks in asynchronous code (one that uses threads etc.) becomes obscure or difficult to follow
	 * Generally, when there is more than one level of indirection, such as code using callbacks, it can become harder to follow, harder to refactor, and harder to test
	 * Raw callbacks sacrifice the control flow, exception handling, and function semantics familiar from synchronous code */


//below is an example of nested callbacks
'use strict'

import request from 'request'
import readline from 'readline'

const io = { input: process.stdin, output: process.stdout }
//Our script is designed to capture user input using stdin (needing a callback)

const read = readline.createInterface(io) 
read.question('input base currency: ', base => { 
// identify whether a currency code is valid (requiring a second callback)
	console.log(`You entered ${base}`)
	read.close()
	base = base.trim()
	// now we need to check the code is valid
	// We want the first request() function (line 21) to be run after the initial read.question() function has completed
	// To do this it needs to be called from inside the read.question() callback function, as we need this data first
	request('https://api.exchangeratesapi.io/latest', (err, res, body) => {
		if (err) {
			console.error(err.message)
			process.exit()
		}
		const rates = JSON.parse(body).rates
		if (!rates.hasOwnProperty(base)) {
			console.error(`invalid currency code ${base}`)
			process.exit()
		}
		// now we can get the currency rates
		// The second request() function should run after the first one has completed and the data has been processed.
		// To do this it needs to be called from inside the callback function of the first request() call, as we need that data first
		request(`https://api.exchangeratesapi.io/latest?base=${base}`, (err, res, body) => {
			if (err) {
				console.error(err.message)
				process.exit()
			}
			body = JSON.parse(body)
			console.log(body)
			// lets ask another question
			const read = readline.createInterface(io)
			read.question('convert to: ', curr => {
				console.log(curr)
				read.close()
				process.exit
			})
		})
	})
})

function strToInt(myString, callback)
//this function will convert a string -> int
{
	let myNumber = parseInt(myString)
  if(isNan(myNumber) == true)
	{
		callback('`${myString}` could not be converted')
	}
	else {
		callback(null, myNumber)
		//null == no error message
	}
}

function toUpper(message, callback)
//this functions will convert a string to uppercase
//itll take to parameters: the string and the callback
{
  if(message.length === 0) 
	{
    callback('zero length string!')
  }
	else {
    const upper = message.toUpperCase()
    callback(null, upper)
  }
}

// function toUpperCallback(err, message)//redundant callback function
// {
//   if(err !== null) {console.error(`ERROR: ${err}`)}
// 	// If there is an error the callback function is called with a single argument which is a message describing the error
// 	else { console.log(message)} 
// }

toUpper('hello world', (err, message) => //we're making use of an anonymous function
{
  if(err !== null) {console.error(`ERROR: ${err}`)}
	// If there is an error the callback function is called with a single argument which is a message describing the error
	else { console.log(message)} }
)