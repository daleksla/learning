/* Once an object has been created, it can be modified in several ways, such as more object values can be added & deleted
 * Additional properties cane be added by setting values by assignment
 * Properties can be removed from an object literal using the 'delete' operator
	 * This removes the entire property
	 * e.g. delete object.property */

const employee = {
  firstName: 'Colin',
  'last name': 'Stephen',
  'department': 'Computing'
}

employee.grade = 4 //this creates an additional property
employee['currently employed'] = true
employee.department = 'Computer Science'