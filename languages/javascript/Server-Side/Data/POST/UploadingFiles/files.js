/* You will also need to enable multipart form processing on the server
 * To convert the mime-type into proper file extensions / intended file extension of upload, you can use the mime-type package
	 * To do so, import the 'mime' module from the 'mine-types' library
	 * ie. import mime from 'mime-types'
 * To access the file, use the ctx.request.files object - this will contain a key for each of the file input
	 * Note: if multiple files are uploaded (ie. if the 'multiple' attribute is set to "true"), the key will contain an array of files
 * Each file includes a few important attributes
	 * 'name' ~ filename of uploaded file
	 * 'type' ~ mime-type (file type)
	 * 'size' ~ file-size (in bytes)
	 * 'path' ~ file-path to temporary directory (called upload)
 * All files get uploaded to a temporary directory (called upload) and are assigned a random hash for a name (no file extension)
	 * The files in this directory are regularly deleted 
	 * If you want to save the file, use the fs.copy() function to copy the file to the appropriate location on the server */

import Koa from 'koa'
import Router from 'koa-router'
import serve from 'koa-static'
import views from 'koa-views'
import bodyParser from 'koa-body'
import fs from 'fs-extra'
import mime from 'mime-types'
//To convert the mime-type into a file extension you can use the mime-type package

const app = new Koa()
const router = new Router()

app.use(serve('public'))
// you need to install the "handlebars" package
app.use(views(`views`, { extension: 'handlebars' }, {map: { handlebars: 'handlebars' }}))
app.use(bodyParser({multipart:true}))
const port = 8080

app.use( async(ctx, next) => {
	console.log(`${ctx.method} ${ctx.path}`)
	await next()
})

router.get('/', async ctx => {
  await ctx.render('files')
})

router.post('/quote', async ctx => {
  console.log(ctx.request.body)
  console.log(ctx.request.files.myfile)
  const myfile = ctx.request.files.myfile //gets file
  myfile.extension = mime.extension(myfile.type) //interpret using mine-type & assign real file extension
  console.log(`original filename: ${myfile.name}`)
  console.log(`mime-type: ${myfile.type}`)
  console.log(`correct file extension: ${myfile.extension}`)
  console.log(`file size (in bytes): ${myfile.size}`)
  console.log(`temp upload directory and name: ${myfile.path}`)
  try {
    await fs.copy(myfile.path, `uploads/${myfile.name}`) //we copy the file from where it is to where we want using a name we want
  } catch(err) {
    console.log(err.message)
  } finally {
    ctx.redirect('/') //we then redirect to root website again
  }
})

app.use(router.routes())
app.listen(port, () => console.log(`listening on port ${port}`))
