/* JavaScript can be used to both add DOM nodes
 * There are some useful methods (of the document object) to help you achieve this:
	 * createElement(element) ~ creates a new DOM node a specififed type (where element is the specified node, such as 'li', 'p' etc.)
	 * appendChild(element) ~ inserts new nodes inside a parent node (where element is the datatype of child node, such as 'li', 'p', etc.) */

document.addEventListener('DOMContentLoaded', event => { //when all content has loaded
  console.log('DOMContentLoaded')
  document.querySelector('input').select() //find first instances of input box and selects it
  document.querySelector('input').addEventListener('keyup', addItem) //detect when a key has been pressed
})

function addItem(event) {
  if(event.key === 'Enter') { //this code in this function will only run if the key entered was 'Enter'
    const name = event.target.value //get value (word) typed in
    const li = document.createElement('li') //creates a new DOM node of a specified type
    li.innerText = event.target.value //set current value being worked on as the value of list element
    li.addEventListener('click', deleteItem) //when a click event happens, call the deleteItem function. 
  //Note: this function will be covered in 'removingNodes.js'
    document.querySelector('ol').appendChild(li) //find the first instance of <ol> element, append a list item to it
    event.target.select()
  }
}