/* When making any HTML, when we create the form, we use the 'get' method to pass the content of the HTML file to the server
	 * GET is used to request data from a specified resource
 * When we submit a HTML form, it triggers a method called 'post'
	 * POST is used to send data to a server to create/update a resource
 * Note: although the HTTP protocol supports many methods, web browsers only support GET and POST 
 * One of the key differences between GET and POST requests is that a POST request includes a body 
	 * This is where the form data is transported
 * In order to be able to access this data (ie. the form body), you will need to include the koa-body package and add this as middleware
 * To make a route respond to a POST request, we use the router.post() function (as oppose to a normal router.get() function) 
 * For how to then use a POST request on a HTML file, read the 'posting.handlebars' file 
 * Eventually, the route.post('/quote') method will be triggered and will subsequenty print the body of data (in this case, to the terminal) 
 * Note: the 'query' property (ie. ctx.query) contains data passed as querystrings */ 

import Koa from 'koa'
import Router from 'koa-router'
import serve from 'koa-static'
import views from 'koa-views'
import bodyParser from 'koa-body'
// One of the key differences between GET and POST requests is that a POST request includes a body 
// This is where the form data is transported
// In order to be able to access this data you will need to install the koa-body package and add this as middleware

const app = new Koa()
const router = new Router()

app.use(serve('public'))
app.use(views(`views`, { extension: 'handlebars' }, {map: { handlebars: 'handlebars' }}))
app.use(bodyParser()) //here we add it as middleware

const port = 8080

app.use( async(ctx, next) => {
	console.log(`${ctx.method} ${ctx.path}`) //this middleware function prints website
	await next()
})

router.get('/', async ctx => {
  console.log(ctx.query.author) //The ctx.query property contains the data passed as querystrings
//here will reprint the author name each time root website runs 
//(note: the first time this function will run, 'undefined will print' - this is due to the fact it prints the last authors name submitted)
const thing = ctx.request.body.password
if(ctx.request.body.password === ctx.request.body.confirmpassword) { //if two password enteries are the same
//		console.log(thing)
	console.log(thing) //print it to the console
}
  await ctx.render('form', ctx.query)
})

router.post('/quote', async ctx => { //here we create a route to respond to a POST request, on the 'insertDomainName/quote' route
  console.log(ctx.request.body) //print body of data
  ctx.redirect(`/?author=${ctx.request.body.author}`) //redirect browser back to home page
  // The URL in the redirect includes a querystring with a key of author and its value coming from the form data
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))
