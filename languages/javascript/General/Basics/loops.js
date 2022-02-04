/* One common task that needs to be carried out with arrays is to iterate (loop) through each of the indexes
 * JavaScript provides a number of mechanisms
	* the first being to use a traditional 'for loop'
	* the second is 'for <index-name> in <array-name>' ~ this will provide the index's 
	* the third is 'for <index-name> of <array-name>' ~ unlike the latter, instead of looping through the array _indexes_ it loops through the array _values_ 
 * We may also desire a loop to run whilst a certain condition is met - this is called a while loop */

let myArray = ["Blue", "Orange", "Green", "Indigo"]
for(let i = 0; i < myArray.length; i++) 
{
  console.log(`${i}: ${myArray[i]}`) //print index / counter value and the indexed value of the array
}

for(let index in myArray) 
{
  console.log(index) //prints index
}

for(let colour of myArray) 
{
  console.log(colour) //prints value
}

while(myArray.length > 1)
{
	console.log(myArray.pop())
}