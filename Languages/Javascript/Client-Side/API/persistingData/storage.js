/* Any data entered in the browser only lasts until the browser is refreshed, then all data is lost
 * All modern browsers can persist data so that it can then be accessed when needed
	 * To do so, we can use the 'Web Storage API', which offers two mechanisms:
		 * sessionStorage ~ persists the data until the tab or browser is closed
		 * localStorage ~ persists the data until it is deleted
	 * Both mechanisms are simple key-value stores and sandbox the data so that it is only available to pages from the domain
 * The API treats both as objects with keys used to store and retrieve the data
 * Note: You can only store primitives (strings and numbers)
	 * However, if you need to store more complex data such as objects and arrays you can convert them to JSON strings 
	 * Don’t forget to convert the string back into the object when you retrieve it! (using the JSON.parse(jsonStringData) */

document.addEventListener('DOMContentLoaded', event => {
  console.log('DOMContentLoaded')
  loadData()
  document.querySelector('input').select()
  document.querySelector('input').addEventListener('keyup', addItem)
})

//this function should see if there is any stored data and convert this to an ordered list
function loadData() {
  const json = window.localStorage.list //get where we would store values
  const data = JSON.parse(json) //parse it back into an object (in this case an array)
  data.forEach(item => { //for each record
    const li = document.createElement('li') //create an item
			li.addEventListener('click', deleteItem) //if the list element is clicked, delete it
    li.innerText = item //give it the value from the array
    document.querySelector('ol').appendChild(li) //add each list element to the list
  })
}

function saveData() { //this is called every time a new item is added
  const items = [...document.querySelectorAll('li')] //nodeList
  const data = []
  for(const item of items) data.push(item.innerText) 
	//for each item in the nodeList, get the text in each one & put it in the data array
  const json = JSON.stringify(data) //convert text-items into a JSON-string
  console.log(json)
  window.localStorage.list = json //put it in local storage
}

function addItem(event) {
  if(event.key === 'Enter') {
    const name = event.target.value //get value entered
    const li = document.createElement('li') //create a new list element
    li.innerText = event.target.value //set the elements text value
    li.addEventListener('click', deleteItem) //if the list element is clicked, delete it
    document.querySelector('ol').appendChild(li) //add the list element into the first block of lists
    event.target.value = '' //reset input field
    saveData() //save the data
    event.target.select()
  }
}

function deleteItem(event) { //we've covered this before - it deletes the item
  console.log('delete item')
  const index = [...event.target.parentNode.children].indexOf(event.target)
  console.log(`item at index: ${index}`)
  this.parentNode.removeChild(this) 
  document.querySelector('input').select()
}
