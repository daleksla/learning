/* One of the most important challenges is to manage code running in multiple threads
 * When a script is executed the code starts running in the main thread
 * However if an operation is likely to be time-consuming (such as reading the contents of a file or accessing a database), we need to push this operation onto its own 'thread'
	 * This is because otherwise we will tie up the main thread, slowing down the perceived speed of the script
 * We can create callback functions, which will essentially store the operation of the code and execute it once it's complete
	 * The first parameter represents any errors that have occurred
		 * If there is no error, it is not assigned a value (null)
	 * The second and other parameters represents the data returned
		 * If there is no data, these are omitted
 * We defined a named function first (our callback to deal with errors and data returned) and then passed it by name as the callback to the main function
 * Note: JavaScript supports first class functions
	 * This means we can use a function in the space where we could use / define a variable */

import fs from 'fs' //pretend this gives us a file to read text files
import getTemp from './temp.js'

function printQuotes(err, data) //where err = error, data = data
{ //this is our callback function
  if (err)
	{
		console.log(err.message)
	}
    let quotesInArray = (data.toString()).split('\n') //note, this function converts the data to a string & split it into array elements
	//the indicator when it's time to split is defined between the brackets - in this case it was everytime a newline tag was used
    console.log(quotesInArray)
}

console.log('code BEFORE the callback')

fs.readFile('./shortquotes.txt', printQuotes) 
//we call the fs module's readFile() function
//it takes two parameters, the name of the file we wanna read & the callback we made

console.log('code AFTER the callback') //when u run the program, this line would run first
//the readFile() function will run after, when the process is complete

function printTemperature(err, data) //again, we create our callback
{
    if(err) 
	{
        console.log(err)
    } 
	else {
        console.log(`the temperature is ${data} celcius`)
    }
}

getTemp('Birmingham', printTemperature) //this function requires a callback, it won't run w/o it - just provide the name
