/* All JavaScript object (e.g. string, mumber) inherit properties and methods from a prototype
 * This also applies to any new objects you create
 * Since JavaScript does not support traditional OOP, prototyping is the alternative
	 * Not only can we add functionality to existing prototypes, we can create our own prototypes too 
 * To use prototypes, place the datatype, following by the prototype keyword, followed by the new function name ; this should be seperated by the dot ('.') operator
	 * e.g. datatype.prototype.myFunction = function() {insert-function-content} */

String.prototype.toArray = function() { //here, we add a function to the strng template
//this function isn't defined anonymously
//this is because arrow functions lack their own context (ie. can't use 'this' keyword)
  const strArr = this.split('')
  return strArr
}
const nameArray = 'John Doe'.toArray() //since 'John Doe' is a string, we can use this new string method we previously created
console.log(nameArray)