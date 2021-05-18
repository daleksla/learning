#include <iostream>
#include <vector>
#include <algorithm>
#include <iterator>
using namespace std ;

/* Iterators are variables that represent a position in a structure.
	 * They are effectively the position AND the value (to fetch value, simply place an '*' beforehand)
 * Similar to pointers in functionality & concept (a lot of iterators are actually pointers behind the scenes)
 * This program will do the following
	 * Start at beginning of vector (or whatever data type the list contains)
	 * Will 'dereference' the iterator & print it's value
	 * Changes value of iterator to the next element in the list/array/linked list etc.
	 * Will repeat the three former steps whilst our 'it' iterator hasn't the same value as the end value
		 * note that the end() function gives us the value right past the last one 
	 * It will then print all the elements backwards, seperated by commas
 * Note: you can iterator backwards as well as forwards
*/

int main()
{
	vector<int> values{ 1, 2, 3, 4 };
	
	for(vector<int>::iterator it = begin(values); it != end(values); it = next(it)) 
	{
		cout << "Value = " << *it << endl ;
		cout << "This is element no. " << distance(begin(values),it) + 1 << "\n "<< endl ;//an external function (distance) that measures the position between one point and another
	}
	
	for(vector<int>::iterator it=prev(end(values)) ; it!=begin(values) ; it=prev(it))
	{
		cout << *it << ", " ;
	}
	cout << *values.begin() << endl ;
	
	//
	return 0;
}