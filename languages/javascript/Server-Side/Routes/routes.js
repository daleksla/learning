/* We can create multiple routes to serve different resources (e.g. displaying different segments of text)
	 * To do so, we additionally require the 'koa-router' package
	 * We then need to create an object of the router
		 * e.g. const router = new Router()
	 * We then use the get method of the Router object
		 * The first parameter should be the end of the URL
		 * The second is a async callback allowing us to manipulate the page 
 * Note: in this file also contains how to sucessfully retrieve files from our directories */

import Koa from 'koa'
//import web-server
import Router from 'koa-router'
//To create multiple routes we need to import the koa-router module
import serve from 'koa-static'
//using this package allows us to make directories public to access resources within

const app = new Koa()
const router = new Router() //create a koa router object

app.use(serve('public'))

const port = 8080

router.get('/', async ctx => { //if URL ends with '/' (ie. nothing)
  ctx.body = '<h1>Home</h1>'
})

router.get('/foo', async ctx => { //if URL ends with '/foo'
  ctx.body = '<h1>Foo!</h1>'
})

router.get('/bar', async ctx => { ctx.body = '<h1>Foobar</h1><figure><img src="/deepthought.png" /></figure>' } )
//if URL ends with '/bar'

router.get('/robot', async ctx => { ctx.body = '<figure><figcap>Marvin</figcap><img src="/marvin.jpg" /></figure>' } )
   //if URL ends with '/robot'
	//note: the webpage will make a http request to get the image 'marvin.jpg'
	//we need to allow the browser to access this directory
	//hence, prior to the code, we set the directory to public

app.use(router.routes()) //we've stored multiple functions to manipulate the webpage in our router object
//therefore we just provide the object's property 'routes', which has stored all our roots
app.listen(port, () => console.log(`listening on port ${port}`))