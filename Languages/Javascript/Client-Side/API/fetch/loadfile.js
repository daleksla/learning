/* The fetch API provides the ability to use JavaScript to make HTTP requests 
 * The 'fetch' function requires one function - the path & file name 
	 * It returns a response object
	 * This includes the status property which contains the HTTP status code*/

document.addEventListener('DOMContentLoaded', async event => {
  console.log('DOMContentLoaded')
  await loadData() //call asynchronous function we make to read from file
})

async function loadData() {
	try {
		const response = await fetch('./quotes.json') //wait for result from async function
		console.log(response)
		console.log(`status: ${response.status}`)
		if(response.status !== 200) throw new Error('failed to import file') //if an error occured
		//below here we process data meaningfully
		const json = await response.json() 
		//The response.json() function takes the response body and parses it into a JavaScript object.
		console.log(json)
		document.querySelector('h1').innerText = json.title //replace website headers with header of JSON file
		json.quotes.forEach( quote => {
			console.log(quote)
		})
	} 
	catch(err) {
		console.error(err.message)
	}
}
