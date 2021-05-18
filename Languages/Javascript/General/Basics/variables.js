/* JavaScript is a loosely typed language
	 * This means that you don’t specify the data type of a variable - it adopts the data type of the value assigned to it
 * The let keyword is used to define a block-level variable
	 * These allow for local variables to be declared in blocks such as loops and branches
 * If the variable is going to be immutable (not change) we should instead use the const keyword 
	 * This will throw an error if the program then attempts to change the value of the variable
 * You should always use this in preference to using the var keyword */

let species = 'Chronicom'
console.log(species)

const name = 'Salih'
// name = 'Bob' //this line will cause the program to crash

// const names = ['Matthew', 'Mark'] //note that this line will not make this array un-modifiable - arrays inherently are modifiable
// therefore all we've done is ensure the variable will always store an array
const names = Object.freeze(['Matthew', 'Mark']) // this line will ensure it will also freeze the content of the variables
console.log(names)


