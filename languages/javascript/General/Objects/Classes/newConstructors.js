/* Whilst constructor functions are not particularly elegant they do provide a way to structure your objects efficiently
 * Recently, JS introduced a cleaner way to work with these using classes
 * To define a class, simply use keyword 'class', followed by the intended class name and the encapsulation of the code within curly brackeets
 * Note: we use the constructor() function, rather than calling the base object preceeded with the 'new' keyword */

class Person {
  constructor(i_name, i_startYear) { //this becomes the default constructor
    this.name = i_name
    const currentYear = 2019
    this.startYear = i_startYear || currentYear
    this.years = currentYear - this.startYear
    return this
  }
}