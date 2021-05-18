/* Objects are containers for named values called properties or methods 
 * The simplest way to create new objects is by creating an object literal which is defining an object and storing it in a variable 
	 * In this instance, it is the Javascript equivalent of using struct's 
 * To create a property-value pair, place a colon (':') between the two, followed by a comma
 * It is also possible to create an empty object (we can add properties later)
	 * This is done by assigning empty curly braces
	 * */

'use strict'

const employee = {
	firstName: 'Colin', //attribute (called firstName) on the left, property on the right
	'last name': 'Stephen', //note that you can use quotation marks in variable names - this bypass the rules regarding naming coventions (such as no spaces)
	gender: 'Male',
	'date of birth': 2000,
	startYear: 2010,
	'department': 'computing',
}