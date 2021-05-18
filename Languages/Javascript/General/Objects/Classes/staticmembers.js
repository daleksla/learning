/* Each instance of a prototype function is completely self-contained
 * However, we may need store data about the prototype itself
 * In a traditional OOP language, we would use static methods and the new ECMA class syntax allows us to do so by adding properties to the prototype function itself
 * We can also define static methods that can be called directly from the prototype function */

'use strict'

class Person {
	static counter = 5 //here we create a static variable 
  constructor(name, startYear) {
    this.name = name
    const currentYear = 2019
    this.startYear = startYear || currentYear
    this.years = currentYear - this.startYear
		counter += 1 //each time constructor is called, counter increases
    return this
  }
  static staticMethod() {
    return this.counter ; //returns counter var
  }
}

const ruth = new Person('ruth')
console.log(ruth.name) //this prints attribute of specific object
console.log(Person.staticMethod()) //we use the class name as the object
// in this example, it'll always print 'static method has been called'