/* JavaScript Object Notation (JSON) is a standard text-based format to represent structured data
	 * This means we can take any JavaScript object and convert it into a text string
		 * This is done using the JSON.stringify() method & by passing it our object
		 * Note: to make it more legible, we can pass two more parameters
			 * The first additional parameter (ie. second parameter) will alter the behaviour of the stringification process
				 * by using null, all the properties of the object are includded in the JSON string
			 * The second additional parameter (ie. third parameter) will insert white space for readability purposes
				 * Note: values less than 1 indicate that no space should be used
	 * We can also takes JSON-text and convert it into a JavaScript object too 
		 * This is done using the JSON.parse() method & passing it our string
		 * Note: the properties and values within the string to be converted to an object must be respectively enclosed in double quotes ('""') */

const jsonstring = '{ "firstName": "Colin", "last name": "Stephen", "department": "Computing"}' //here we create the content of our JSON string
//note that all properties & values within are in double quotes
const employee = JSON.parse(jsonstring) //here we use the parse() method of JSON to create an object and store it in a const

jsonstring = JSON.stringify(employee, null, 2)
//this function will take our JSON object & include white spaces - finally it'll save it to a string called jsonString