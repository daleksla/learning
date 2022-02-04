/* Arrays are specials variables thhat can hold more than one value
 * They operate similarly with regards to creation & operation to lists in Python
	 * To create an array, enclosed your vales in square brackets ([]) and seperate the values with commands
	 * To access a specific value (be that to modify or assign, use the [] operator, with the index value inbetween
 * There are multiple methods we can use on arrays to modify them:
	 * push(<value>) ~ add value to the end of the array
	 * unshift(<value>) ~ adds a value to the start of the array
	 * pop() ~ removes and returns the value from the end of the array
	 * shift() ~ removes and returns the value from the start of the array
	 * length ~ provides length of array 
*/
//create array
let myArray = []

//add values to the array
myArray.push("Red")
myArray.push("Blue")
myArray.push("Yellow")

console.log(myArray) //prints array
console.log(myArray.length) //print length of array

console.log(myArray.pop()) //remove last view from array & print it