/* We can create methods for objects whoch will operate differently based on the object that called it
 * This can be achieved using the 'this' keyword when accessing values
	 * For example, if 'object' called the 'function' method (e.g. object.function()), the 'this' variable within would represent 'object' */

'use strict'

const obj1 = { name: 'Kent', print: print,} //here we set a method for the object called print ; the object will be able to call it
const obj2 = { name: 'Cornwall', print: print,}

function print() {
	console.log(this)
}

print() //this isn't called as a method (ie. it's called like a normal function)
//because of this, 'this' will not have any value, therefore it won't print anything as it's undefined

obj1.print() //this will print obj1 values
obj2.print()//this will print obj2 values