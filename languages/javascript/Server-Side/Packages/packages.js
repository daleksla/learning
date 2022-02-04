/* Packages comprise of code that contain functionality written by other developers that you can use in your code
	 * Some are already installed and just need importing
	 * Others are called 'third party modules' (using the Node Package Manager (npm)) and need to be installed manually
		 * Important packages such as node-fetch is one of these */

import Koa from 'koa'
import https from 'https'

const app = new Koa()

import fetch from 'node-fetch' //this package is used to send HTTP requires
//note: the data returned will be in JSON format

const port = 8080

app.use(async ctx => {
	const response = await fetch('https://pokeapi.co/api/v2/pokemon')
	//fetch() function to make an http request to the PokéAPI url
	//The http response is stored in the response variable
	const json = await response.json()
	// The response.json() function takes the response body and replies with a json object which we store
	console.log(json)
	//this will print our JSON object into the TERMINAL
	ctx.body = `<pre>${JSON.stringify(json, null, 2)}</pre>`
	//we now turn our json object into a string
	//we pass it to the property 'body' of the object 'ctx' - we enclose it with <pre></pre> tags to preserve newlines, indentation etc. 
	//this will print it to the client (webpage)
})

app.listen(port, () => {
  console.log(`listening on port ${port}`)
})