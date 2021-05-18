class Human:
	def __init__(self, i_name, i_age):
		self._name = i_name 
		self._age = i_age 
	
	def returnName(self):
		return self._name
	
	def returnAge(self):
		return self._age	

def main():
	human = Human("Salih", 19)
	assert human.returnName() == "Salih", "returnName test #1: Should be 'Salih'"
	assert human.returnName() != "Talih", "returnName test #2: Shouldn't be 'Talih'"
	assert human.returnAge() != 6, "returnAge test #1: Shouldn't be 6"
	assert human.returnAge() == 19, "returnAge test #2: Should be 19"

if __name__ == "__main__":
	main() 
	print("Everything passed") #will crash if assertion isn't true