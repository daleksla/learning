def add(myList):
	mySum = 0
	for i in myList:
		mySum += i
	return mySum

def main():
	assert add([1, 2, 3]) == 6, "add test #1: Should be 6"
	assert add([2, 2, 3]) != 6, "add test #2: Shouldn't be 6, rather it should be 7"

if __name__ == "__main__":
	main() 
	print("Everything passed") #will crash if assertion isn't true