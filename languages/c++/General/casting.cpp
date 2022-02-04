#include <iostream>
using namespace std;

/* Static Casting is used to make a variable able to store a new data type
 * This can be done for a host of reasons, such as with calculations etc. */

int main()
{
	int num = 7 , factor = 2 ;
	char letter = 'A' ;
	float result = 0.0 ;

	// Plain division.
	cout << "Integer division: " << ( num / factor ) << endl ;

	// Cast int to float.
	result = (float) (num) / factor ;//old method of casting ; num (int) converted into a float before calculation
	cout << "Cast division float: " << result << endl ;

	// Cast char to int.
	num = static_cast <int> (letter) ; //new method of casting ; changing letter (char) into an int variable#
	//NOTE: converting char->int/int->char reveals it's equivalent on the ASCII table
	cout << "Cast character int: " << num << endl ; //

	// Cast int to char.
	letter = static_cast <char> (70) ;
	cout << "Cast integer char: " << letter << endl ;

	return 0 ;
}