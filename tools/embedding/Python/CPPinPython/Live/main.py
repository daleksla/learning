"""This program makes use of the module 'kitty' we wrote in C++"""

from kitty import * 

def main():
	garfield = kitty() #create object from class 'kitty'
	garfield.speak2() #call it's method

if __name__ == '__main__':
	main()