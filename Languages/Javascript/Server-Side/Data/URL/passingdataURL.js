/* When building a dynamic website, an important techniques is to be able to pass and retrieve data using the URL 
 * This file demonstrates how to extract data from the URL
 * Take a look at the HTML files, specifically the subpages.handlebars file, to see how the data is used */

import Koa from 'koa'
import Router from 'koa-router'
import serve from 'koa-static'
import views from 'koa-views'

const app = new Koa()
const router = new Router()

app.use(serve('public'))
// you need to install the "handlebars" package
app.use(views(`views`, { extension: 'handlebars' }, {map: { handlebars: 'handlebars' }}))

const port = 8080

router.get('/', async ctx => {
  await ctx.render('numbers')
})

router.get('/number/:id', async ctx => {
	//when any redirect occurs, the URL will pseudo-match the URL for this route & therefore this route will be called
	//when the sub-URL '/number' is used, anything after that part will be sort 
	//it will automatically in the 'params' object (ie. ctx.params)
  console.log(ctx.params) //print params object to screen
  const data = {number: ctx.params.id} //we get the id property of the params object
	//we then associate the number property with this value
  await ctx.render('subpages', data) 
	//note: render() allows us to call our handles (template) webpages
	//first param == file to call
	//second param == object for it to use
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))
