/* ECMAScript modules are the official standard format to package JavaScript code for reuse
 * Modules are defined using a variety of import and export statements
 * Modules contain ordinary JavaScript and so use the .js file extension
 * However some developers prefer to use the .mjs extension to clearly distinguish between standard JavaScript code and modules
 * All code in a module is private unless specifically made public using the 'export' keyword
	 * To export a function, preceed the function header with the 'export' keyword
		 * e.g. export function myFunction() {...}
	 * When we import a module with a default export, we import it into an object with a name of our choosing
	 * To set a function / object as a default export, preceed the 'export' keyword with 'default'
		 * e.g. default export myFunction() {...}
 * To import a module, simply use keyword 'import', followed by the name of the function you're importing, followed by it's location 
	 * e.g. import {myFunction} from './myModules.mjs' */

//assume this section is the normal.js file
import {longest} from './module.mjs' //imports the function longest
import {randomPrint as printStuff} from './module.mjs' //import function with a different name
import temp from './temp.js' //this imports our default export and saves it in the name temp

//assume this section is the module.mjs file
export function longest(names) 
{
	let bigString = ''
	for (const name of names) {
		if (name.length > bigString.length) bigString = name
	}
	return bigString
}

export function randomPrint()
{
	console.log('Hi!') ;
}

//assume this section is the temp.mjs file
export default function getTemp(location, callback) //this will be the default export
{
	const base = 'https://api.openweathermap.org/data/2.5/weather'
	const appID = '44c39f3fa462f86b3fc88f5678e5c5ff'
	const url = `${base}?q=${location},uk&appid=${appID}`
	https.get(url, response => {
		response.on('data', data => {
			const info = JSON.parse(data.toString())
			if(response.statusCode !== 200) {
				callback(info.message)
			} else {
				callback(null, parseInt(info.main.temp - 273))
			}
		})
	})
}
