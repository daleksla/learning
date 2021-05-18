#include <iostream>
#include <string>
using namespace std ;

/* Create variables, reference to memory & manipulate 
 * references are NOT variables in their own right. they merely an alias for a variable - cannot be reassigned
 * must be initialized (given value) during declaration (like a constant) */

int main()
{
	int num = 100 ; //create variable
	int& numReference = num ; //use & symbol instead of * to create reference
	//
	cout << numReference << endl ; //prints value (as references just... reference to a value, rather than hold an address) 
	cout << &numReference << endl ; //prints memory address of reference 
	//
	numReference = 400 ; //change value of 'reference' (actual value)
	cout << numReference << endl ; //prints value (as references just... reference to a value, rather than hold an address) 
	cout << &numReference << endl ; //prints memory address (should be the same)
	//
	return 0;
}