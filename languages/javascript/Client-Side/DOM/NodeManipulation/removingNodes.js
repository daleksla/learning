/* JavaScript can be also be used to remove DOM nodes
 * Note:
	 * event.target.parentNode.children is a property that returns a nodeList of all childNodes of the specified parentNode 
	 * parentNode.removeChild(value) is a function that will remove a childNode of a parentNode with a specific value */

//...the following code is from the function 'addItem()' in the 'addingNodes.js' file
    li.addEventListener('click', deleteItem) //when a click event happens, call the deleteItem function. 

function deleteItem(event) {
  console.log('delete item')
  const index = [...event.target.parentNode.children].indexOf(event.target)
	//event.target.parentNode.children gives us the collection of child nodes in a nodeList
	//we then place it into an array by placing [] around the property
	//we use the indexOf(event.target) function to then go through the array trying to find a specific value (in this case a specific element)
  this.parentNode.removeChild(this) 
	//To delete a node we need to get a reference to its parent using this.parentNode
	//then we remove the selected item from the parent using its removeChild() function
  document.querySelector('input').select() //we then find the next input & select it again
}
