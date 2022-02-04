/* Most objects properties are simple values which you can set and retrieve
 * However, sometimes properties need to be calculated or manipulated etc. before they can be returned
	 * This is why we create 'getter' functions
 * In the same manner, some properties when set may need to change other properties
	 * This is why we create 'setter' functions */

const employee = {
  firstName: 'Colin',
	
  lastName: 'Stephen',
	
  startYear: 2012,
	
  getName() 
  {
    return `${this.firstName} ${this.lastName}` //returns both first and second name in a string seperated by a space
  },
	
  setName(fullname) 
  {
    const words = fullname.toString().split(' ') //this will take a string, split it with a space
    this.firstName = words[0] || '' //sets value before space as first name, if it doesn't exist set as '' (ie blank)
    this.lastName = words[1] || ''
  }
}
