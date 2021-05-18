/* The constructor method is a special method of a class for creating and initializing an object of that class
 * Whilst this is not now considered the optimal way to achieve the goal of creating more than one object of the same type, it is important you understand both the syntax and how it works
 * When we use this approach, using the 'new' keyword (followed by the struct name), the following occurs:
	 * We create an empty object
	 * We set the its prototype property to the constructor function’s prototype function
	 * We bind its this object to the new object
	 * We then return the new object 
 * We can then save this object in a variable */

function Person(name, startYear) {
    const currentYear = 2019
    this.name = name
    this.startYear = startYear || currentYear
    this.years = currentYear - this.startYear
}

const colin = new Person('colin', 2012) //it will show it is also an instance of 'Person'
console.log(colin)