/* Destructuring is the term used when we retrieve values of specific properties 
 * To retrieve a specific property value there are two options
	 * If the name is a legal JS variable name the dot ('.') notation can be used 
		 * e.g. object.property
	 * If the name is not a valid JavaScript variable name we need to turn it into a string by using quotes '' and enclose it in square braces []
		 * e.g. object[property] 
 * If you try to retrieve a property's value that doesn't exist, you can use the or operator ('||') to serve a substitue if it's not found
	 * e.g. const myConst = object.property || 'alternate value' // this will store 'alternate value' in the myConst variable if property isn't a valid property of object 
 * Note: if you try to retrieve a value from an object that is undefined, JS throws a TypeError exception 
	 * The and operator ('&&') can be used to guard against this problem
	 * It is reffered to as the guard operator because the 1st expression safeguards the 2nd expression
		 * In other words, only if the 1st expression is truthy, then will the 2nd expression be evaluated */

const employee = { //here we create our class
  //note: storing objects in a const is similar how array's are stored in that the values within can be changed, but the datatype within cannot
  firstName: 'Colin',
  'last name': 'Stephen',
  'department': 'Computing',
}

console.log(employee) //this will print a string representation entire object

const firstName = employee.firstName //this will 
const lastName = employee['last name']
const grade = employee.grade

for(const prop in employee) //this will print every property name in the employee object 
{
  console.log(prop)
}

employee.firstName = 'Salih' //despite being a const, we can modify the variables property
console.log(employee.firstName)

const university = {
	year1: ['4000CEM', '4001CEM', '4002CEM', '4003CEM', '4004CEM', '4005CEM', '4006CEM', '4007CEM'],
	year2: ['5000CEM', '5001CEM', '5004CEM'],
}

const study01 = university.year1

for(const prop in university)
{
	console.log(study01)
}

const {firstName: first, 'last name': last, department: dept} = employee
//this is another method to create multiple variables storing various properties of the class on the right side of the equals ('=') symbol