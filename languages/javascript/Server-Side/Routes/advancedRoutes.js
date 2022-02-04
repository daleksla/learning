/* For organisational & legibility purposes, it's important we store relevant routes seperately
 * The solution is to organise your routes into multiple files based on their purpose
 * This file is an example of creating multiple routes in different files, exporting, importing & combining them into an object for usage
 * An advantage is that we can, for example, make use of middleware and assign it only to specific routes
 * Note: read the file from top (creating routes) to bottom (executing script) */

///////////////////////////////////
//pretend below this is filea.mjs//
///////////////////////////////////

import Router from 'koa-router'

const router = new Router()

async function url(ctx, next) {
	console.log('URL MIDDLEWARE')
	url = `https://${ctx.host}${ctx.path}`
	console.log(url)
	await next()
}

router.use(url)

router.get('/', async ctx => {
	ctx.body = '<h1>PAGE ONE</h1>'
})

export default router 

///////////////////////////////////
//pretend below this is fileb.mjs//
///////////////////////////////////

import Router from 'koa-router'

const router = new Router({ prefix: '/two' }) 
//all routes in this file (or whatever uses this object name) will automatically insert '/two' after the main domain name

async function middleware(ctx, next) {
	console.log('MIDDLEWARE: TWO')
	await next()
}

router.use(middleware) //we can provide our router object middleware to use that will only be used by routes beginning with '/two/...'

router.get('/', async ctx => { //ie. https://maindomain.extension/two/
	ctx.body = '<h1>PAGE TWO</h1>'
})

router.get('/subpage', async ctx => { //ie. https://maindomain.extension/two/subpage
	ctx.body = '<h1>SUBPAGE</h1>'
})

router.get('/newRoute', async ctx => { ctx.body = '<h1>NEW ROUTE</h1>'}) //ie. https://maindomain.extension/two/newroute

export default router

/////////////////////////////////////
//pretend below this is routing.mjs//
/////////////////////////////////////

import Router from 'koa-router'

import router1 from './routesOne.js' //import the routers
import router2 from './routesTwo.js' //""

const mainRouter = new Router() //create an object to store our main routes

const nestedRoutes = [router1, router2] 

for (const router of nestedRoutes) { //essentially we append each route to a main router
	mainRouter.use(router.routes())
	mainRouter.use(router.allowedMethods())
}

export default mainRouter //export compiled router

/////////////////////////////////
//pretend below this is main.js//
/////////////////////////////////

import Koa from 'koa'
import Router from 'koa-router'

import router from './routing.js'

const port = 8080
const app = new Koa()

app.use(router.routes()) //provide with routes
app.use(router.allowedMethods())

app.listen(port, async() => console.log(`listening on port ${port}`))

