"""This program teaches us the basics of inheritance
   Inheritance is useful when we want to retain some of the methods & attributes of one class
   In this program we inherit from one class and take one function (printname) but overwrite the constructor
   In line with this, we'll learn how to restrict access to certain variables (and functions)"""

class Person:
  def __init__(self, fname, lname, idob):
    self._firstname = fname #using one underscore makes it a protected attribute (only accessed via a class' methods or subclass')
    self.__lastname = lname #using two underscores makes it a private attribute (only accessible via a class' methods)
	self.dob = idob #no prefixing underscores indicate a public attribute 

  def printname(self):
    print(self.firstname, self.lastname)

class Student(Person): #inherit from parent class (takes it's attributes & functions)
    def __init__(self, fname, lname, schl): #overwriting old constructor
	#super().__init__(fname, lname) 
	#if we wanted to, the super() function allows us to inherit everything from the parent, but we don't
    	self.firstname = fname 
		self.lastname = lname
		self.school = schl
		
