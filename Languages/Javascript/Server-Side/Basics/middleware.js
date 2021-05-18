/* All Koa applications comprise a series of middleware functions that are executed in order
 * Each function takes two arguments:
	 * The koa context object (ctx) that contains a reference to the http request and response
	 * A function called next() that is used to trigger the next piece of middleware
		 * Note: we do not need to provide or call the next function if it's the last middleware we'll provide
 * There are some prebuilt middleware components that you can use to handle common tasks
 * To add a piece of middleware to the server we simply pass the function name to app.use() after we've defined them
	 * These are run in the order they are added to the code
 * Note: the context object contains a lot of useful properties we can use */

import fs from 'fs'
import https from 'https'
import Koa from 'koa'
const app = new Koa()

async function date(ctx, next) { 
	//ctx represents koa context ; next represents function to call next middleware
	console.log('DATE MIDDLEWARE') //prints current name of function in terminal
	ctx.date = (new Date()).toLocaleDateString('en-GB')
	await next() //function call
	
async function url(ctx, next) {
	console.log('URL MIDDLEWARE')
	ctx.url = `https://${ctx.host}${ctx.path}` //here's an example of accessing useful properties of the context (ctx)
	await next()
}
	
async function logger(ctx, next) {
	// this function I made print's each request to the screen
	const timeStamp = (Math.round((new Date()).getTime() / 1000)).toString()
	const currentURL = `https://${ctx.host}${ctx.path}`
	const newThing = timeStamp.concat(timeStamp, ':', currentURL, '\n')
// 	console.log(newThing) //this will print the string
	await fs.promises.appendFile('./serverlog', newThing ) //this mode will add it to a text file
	await next() //remember to call next piece of middleware!
}

async function routes(ctx) {
	console.log('ROUTES MIDDLEWARE')
	console.log(ctx.url)
	console.log(ctx.date)
	console.log(`path: "${ctx.path}"`)
	switch(ctx.path) {
		case '/':
			ctx.body = '<h1>Home Page</h1>'
			break
		case '/login':
			ctx.body = '<h1>Login Page</h1>'
			break
	}
}
	
app.use(date)
app.use(url)
app.use(logger)
app.use(routes)

const port = 8080
app.listen(port, () => console.log(`listening on port ${port}`))