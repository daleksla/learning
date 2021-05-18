/* Most of the time we will only be using a given callback function once
 * We can simplify our code by inserting the function expression itself as the callback parameter 
 * This is better in single-cases than storing it in a variable and using that variable etc. */

import fs from 'fs' //assume this module contains file reading-capable functions
import getTemp from './temp.js'

// const printQuotes = (err, data) =>  //redundant
// {
//   if (err) console.log(err.message)
// 	else {
// 		let quotes = data.toString().split('\n')
// 		console.log(quotes)
// 	}
// }

// fs.readFile('./shortquotes.txt', printQuotes)

fs.readFile('./shortquotes.txt', (err, data) => //place callback function directly as second parameter
{
  if (err) console.log(err.message)
  else { let quotes = data.toString().split('\n')
  for(let i of quotes)
		console.log(i)} //print each element of the array seperately
})

fs.readFile('./shortquotes.txt', (err, data) => //place callback function directly as second parameter
{
  if (err) console.log(err.message)
  else { 
	  let quotes = data.toString().split('\n')
	  for(let i of quotes) //print each element of the array seperately
	  {
		//note, the code below will seperate quotes
		for(let quote of quotes) 
		{ //iterate through list
		  const [author, text] = quote.split(' - ') //split list into sections using ' - ' substring
		  console.log(`"${text}" (${author})`) //print the two seperately
		}
	  }
	}
}
)
