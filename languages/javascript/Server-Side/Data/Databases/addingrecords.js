/* Whilst there any many different databases available, one of the best for developing your website is SQLite
	 * This is a file-based database where the entire database is saved in a single binary file
	 * To use SQLite, use the 'sqlite-async' library
 * The constructor parameter has a default value of :memory:
	 * Using this value tells the database to run in-memory rather than saving to a file
	 * Note: its great for use in your system as it runs much faster
 * When executing a statement to insert, delete, update data, use the databaseObject.run(statement) method
 * When executing a statement to get data, use the databaseObject.all(statement) method */

import sqlite from 'sqlite-async' //import sqlite
import Koa from 'koa'
import Router from 'koa-router'
import serve from 'koa-static'
import views from 'koa-views'
import bodyParser from 'koa-body'

const port = 8080
const dbName = 'quotes.db'

const app = new Koa()
const router = new Router()

class Quotes {
  constructor(dbName = ':memory:') { //constructor's parameter is the file path +/ db name
		return (async() => {
			this.db = await sqlite.open(dbName) //we call an SQL function to open file
			// we need this table to store the user accounts
			const sql = 'CREATE TABLE IF NOT EXISTS quotes\
				(id INTEGER PRIMARY KEY AUTOINCREMENT, author TEXT, quote TEXT);'
			await this.db.run(sql) //execute sql modification
			return this
		})()
	}
  
  async add(author, quote) { //this method adds to database
    const sql = `INSERT INTO quotes(author, quote) VALUES("${author}", "${quote}")` //execute code with injection
    console.log(sql) //print what's getting entered
    await this.db.run(sql) //execute statement
    return //return to where it was called
  }
	
  async getAll(author, quote) { //this method gets all records from database
    const sql = `SELECT * FROM quotes`
    const value = await this.db.all(sql) //run & extract data
    return value
  }
  
  async close() { //at end of file, close database
    console.log('closing database')
		await this.db.close()
	} 
}

app.use(serve('public'))
// you need to install the "handlebars" package
app.use(views(`views`, { extension: 'handlebars' }, {map: { handlebars: 'handlebars' }}))
app.use(bodyParser())

app.use( async(ctx, next) => {
	console.log(`${ctx.method} ${ctx.path}`)
	await next()
})

router.get('/', async ctx => {
  await ctx.render('form')
})

router.post('/quote', async ctx => {
  console.log(ctx.request.body)
  const quotes = await new Quotes(dbName) //make new Quotes() object using class (constructor is async, so wait)
  //then store object in quotes
  await quotes.add(ctx.request.body.author, ctx.request.body.quote)
  //call add method, provide form values
  await quotes.close() //close db connection using method
  ctx.redirect('/') //redirect to subdomain/route '/' (ie. nothing after main domain)
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))
