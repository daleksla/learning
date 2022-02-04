"""This program teaches us the basics of classes and how they work in Python"""

class Person: #class name
  def __init__(self, name, age): #self, refers to current instance of class
    self.name = name 
    self.age = age

  def myfunc(self):
    print("Hello my name is " + self.name)

p1 = Person("John", 36) #calls constructor and stores as a variable (object)
p1.myfunc() #calling object method
del p1 #deletes object

class School:
  pass #allows us to define a class without implementing it w/o error; esp good for inheritance