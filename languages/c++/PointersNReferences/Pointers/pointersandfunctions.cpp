#include <iostream>
using namespace std ;

/* Using pointers to change memory directly & how to pass it's value ; 
 * allows one to bypass need to return and clone data for each function */

void printValue(int* value)
{
	cout << "Value = " << *value << "; located at " << value << endl ;
}

void changeValue(int* value)
{
	*value *= 3; //dereference pointer, multiply it's content by 3 (actual value * 3, replaces old value)
}

int main()
{
	int num = 5 ;
	int* pointer = &num ;
	printValue(pointer) ; //print original value & memory
	changeValue(pointer) ; //changes value of the content of which the pointer.... points to
	printValue(pointer) ; //prints the (should-be) updated value & yet the same memory address 
	//
	return 0 ;
}