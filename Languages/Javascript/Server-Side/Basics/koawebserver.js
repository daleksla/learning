/* All web pages need to be served over HTTP 
	 * We need to install a package that allows NodeJS to be able to listen for HTTP requests and send resources back to the browser
	 * The software that performs this task is called a web server
	 * We will use the Koa webserver */

import Koa from 'koa' //import koa module
const app = new Koa() //create an object

const port = 8080 // this starts the web server which is available on port 808

app.use(async ctx => { //this displays on the website - calling method
//app.use is a function which takes a single async callback
//each time the client (web browser) sends a request it runs the code in the callback
  ctx.body = '<h1>Body</h1>'
})

app.listen(port, () => { //this will display on the terminal
  console.log(`listening on port ${port}`) 
})