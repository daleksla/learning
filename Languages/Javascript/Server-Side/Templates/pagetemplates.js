/* Page layouts allow us to build complex page layouts and include data from the server
	 * We can design our page in HTML and create 'placeholders' where we need data to be inserted
 * We will be using the Handlebars templating engine 
	 * The technical name used for Koa templates is views and Koa uses the koa-views package to manage templates 
	 * We must import koa-views to be able to use templates
	 * Each HTML-esque file where we use the Handlebars engine will have a '.handlebars' extension 
 * To use templates with Koa, we use the 'use' method
	 * We need to specify the directory where the HTML file is located,
	 * The file extension our template will use
	 * The template engine to use 
 * To then use the template, we must use the 'render' method (ie. ctx.render())
	 * The first parameter this method takes is the name of the template file (without file extension)
	 * The second parameter is the object containing data to insert into the template 
 * To see how write the HTML template, go to the template.handles file */

import Koa from 'koa'
//to use webserver
import Router from 'koa-router'
//To create multiple routes we need to import the koa-router module
import serve from 'koa-static' 
//using this package allows us to make directories public to access resources within
import views from 'koa-views'
//to use 'templates'
import fs from 'fs-extra'
//text file stuff

const app = new Koa()
const router = new Router() //create router object

app.use(serve('public')) //make current directory content public
// you need to install the "handlebars" package
app.use(views(`views`, { extension: 'handlebars' }, {map: { handlebars: 'handlebars' }}))
//here we import our template into koa using the use method (ie. koaObjectName.use())
//we mention the directory it'll be in, the file extension & the template engine we're using

const port = 8080

router.get('/', async ctx => {
  const data = { //here is how we format our data object - as property-value pairs
    title: 'Fools Day',
    date: '01/04/20',
	names: ['Salih', 'Enoch']
  }
  await ctx.render('home', data) 
	//here we allow our template to be used in a route
	//the ctx object has a method called render - this is how we'll do so
	//the first parameter is the name of the template file to use (without extension)
	//the second (optional) contains the data object we wish to insert
})

router.get('/quotes', async ctx => {
  const json = await fs.readJson(`./public/quotes.json`)
  console.log(json)
  await ctx.render('quotes', json)
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))
