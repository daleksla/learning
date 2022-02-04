/* Websites may need to keep track of your visits for various reasons (such as seeing if you have logged in etc.)
 * To do so requires the use of 'web cookies'
	 * These are small packets of information that a web server can store inside the client (ie. a user's web-browser)
	 * Once stored, it is attached to every subsequent request made by the browser
 * Cookies can be created, modified & deleted 
 * Note: when cookies are created in the browser, they are encrypted and can only be decrypted by webpages of the same domain name */

import Koa from 'koa'
import Router from 'koa-router'
import session from 'koa-session'
//this 'session' package provides middleware that allows the script easy access to the cookie data through the ctx.session object

const app = new Koa()
const router = new Router()
app.keys = ['darkSecret']
app.use(session(app))

const port = 8080

router.get('/', async ctx => {
	console.log(`ctx.session.authorised: ${ctx.session.authorised}`)
	console.log(`ctx.session.name: ${ctx.session.name}`)
	let body = '<h1>Home</h1>'
	if(ctx.session.name) {
		body += `<p>welcome ${ctx.session.name}</p>`
	}
	if(ctx.session.authorised) {
		//if our current session is authorised, this content is displayed
		body += '<p>You are logged in...</p>'
	}
  ctx.body = body
})

router.get('/login', async ctx => {
  ctx.body = '<h1>Login</h1>'
	ctx.session.authorised = true
	//here we authorised property to this object
	return ctx.redirect('/')
})

router.get('/logout', async ctx => {
  ctx.body = '<h1>Logout</h1>'
	delete ctx.session.authorised
	//here we delete the authorisation property
	return ctx.redirect('/')
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))