/* In our 'basicReference.js' file, we used the 'document' objects 'querrySelector' method to manipulate the first instances of each CSS selector we passed
 * However, we can select all instances of a CSS selector using the 'querySelectorAll' method
	 * This will return an array-like collection of all the DOM elements matching the selector string passed
	 * Note: The 'array-like' structure returned is called a 'nodeList' - it does not have built-in functions like an array does!
 * Since we need to be able to loop through the nodeList and access each node in turn, we can use the built-in forEach() functiom
	 * This takes a callback function which is run on each node */

window.addEventListener('DOMContentLoaded', event => {
	document.querySelectorAll('dt').forEach( term => {
	  console.log(term.innerText)
	})
	document.querySelectorAll('dt').forEach( term => {
	//this formats each <dt> element with the .person class
		term.classList.add('person')
	})
})