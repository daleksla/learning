/* We need to know how to select a specific node we wish to manipulate
 * We can select elements based on their:
	 * name
	 * class
	 * attribute
 * The 'document' object represents the entire DOM tree
	 * It has a method called 'querySelector' - this accepts a single string represents what we want to manipulate (ie. the CSS selector) (e.g. 'h1' etc.)
		 * This function returns the first DOM element that matches the query selector 
	 * Note: if you have several nodes that match the others will be ignored - we'll deal with this later 
 * To change the appearance of your web page (using JavaScript), first define the appearance in the CSS stylesheet as a class (ie. .className {...}) and then use JavaScript to add or remove this class
	 * The classlist object we use to do this very useful
	 * It contains several functions:
		 * classList.add('className') ~ add the className class to the element
		 * classList.remove('className') ~ removes the className class 
		 * classList.toggle('className') ~ add the className class if missing or removes it if its already assigned
		 * classList.replace('className', 'otherClassName') ~ replaces the className class with the otherClassName class */

window.addEventListener('DOMContentLoaded', event => {
	//Since we are manipulating the DOM it needs to load before the script runs
	//Therefore we put our code in the callback function that is triggered when the DOM is loaded (ie second param of event handler)
	console.log('DOMContentLoaded')
	const heading = document.querySelector('h1')
	//here we use a CSS selector to get a reference to the top-level heading node and store this in a variable which is printed to the browser console
	console.log(heading)
	heading.innerText = 'Famous Quotes'
	//The innerText property represents the text inside a DOM node so we use it on line 10 to change the text displayed in the heading (even if something else was meant to be there)
	window.setInterval( () => {
		heading.classList.toggle('purple')
		}, 5000
	)
	//The window.setInterval() function takes a callback that is run at specific intervals
	//The length of the interval in milliseconds is passed as the second parameter (after the callback)
	//we essentially keep triggering and untriggering the 'purple' class
	window.setTimeout( () => {
	//Use the setTimeout() function to make the top-level heading 4em high 3 seconds after the page loads
	//unlike the setInterval() function, it only run's once
		heading.classList.add('big')
		}, 2000
	)
	const aside = document.querySelector('aside')
	//here we make the first <aside> tag bold
	aside.classList.add('strong')
})
