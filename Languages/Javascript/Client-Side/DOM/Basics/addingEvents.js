/* Here we will add event handlers to parts of the DOM to respond to user interaction
 * Having selected a DOM node (using document.querySelector()), we use the addEventListener() function to attach the required event handler
	 * The first parameter is a string representing the event name
		 * There are many different events recognised by the DOM, such as:
			 * click ~ the user clicks on the element (or taps on a touch-screen)
			 * change ~ the value of a form element changes
			 * keyup ~ the user presses a key on the keyboard and releases it
				 * Note: if the event was not triggered by the keyboard this returns null
	 * The second parameter is the callback that will be run when the event is triggered
 * The callback takes a single parameter - this is an object representing the event triggered
	 * This object has three properties:
		 * event.type ~ name of the event triggered
		 * event.target ~ reference to the object that triggered the event
			 * This has properties such as 'value' (ie. the value of the target element)
		 * event.key ~ contains the name of the key that was pressed on the keyboard
			 * Note: the value is null if the event was not triggered by a keypress
	 * These three properties provide all the information needed to process the event */

document.addEventListener('DOMContentLoaded', event => {
  console.log('DOMContentLoaded')
  
  // simple event handler - note that it only run when full content is loaded
  document.querySelector('input[type="submit"]') //here we get the DOM node (first instance)
    .addEventListener('click', event => { //we add an event in the event 'click' occurs
		//below is the callback that's called
      event.preventDefault()
      console.log(`event detected: ${event.type}`)
      console.log(event.target)
      console.log(`node type: ${event.target.nodeName}`)
      console.log(`"name" attribute: ${event.target.getAttribute('name')}`)
  })
	
	const selectAttribute = document.querySelector('select')
	selectAttribute.addEventListener('change', (event) => {
		console.log(event.target.value) 
		//remember that the DOM element is stored in the event.target object and the value of a form element is accessed using the value property.
	})
	
	document.querySelectorAll('input, select, textarea').forEach( select => { //here, we select all input, selection & text area DOM nodes
		select.addEventListener('change', event => { //if any change occurs ...
			console.log(`${event.type} event`) //print the name of event
			console.log(event.target.getAttribute('type')) 
			console.log(event.target.getAttribute('name'))
			console.log(event.target.value) //print value 
			console.log(event.target.checked)
		})
	})	
})