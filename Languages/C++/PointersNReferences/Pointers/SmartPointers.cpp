#include <algorithm>
#include <memory>
#include <stdexcept>
#include <iostream>
using namespace std ;

/* Smart pointers: they automatically deallocate memory when not pointing at an address 
 * Wrapper around raw pointers
 * Don’t need to remember to delete & therefore no memory leaks
 * They have 99% of the same functionality as normal pointers 
 * Three types : shared_ptr, unique_ptr, weak_ptr
	 * shared_ptr - retains shared ownership of an object through a pointer
	 * unique_ptr - just like shared_ptr, but only one of these types can point to one object
	 * weak_ptr - isn't bloody needed rn */

int main()
{
	shared_ptr<int> pointerA = make_shared<int>();
	*pointerA = 42;
	cout << *pointerA << endl ; //will print value it points to
	cout << pointerA.use_count() << endl; // result: 1 
	// use_count() function counts how many pointers point to an object 

	shared_ptr<int> pointerB = pointerA; //pointerB points to pointerA is pointing to
	cout << pointerA.use_count() << endl; // result: 2
	pointerB = nullptr; //make pointerB pointer somewhere else instead
	cout << pointerA.use_count() << endl; // result: 1
	
	unique_ptr<char> pointerC = make_unique<char>();
	*pointerC = 'c' ;
	//unique_ptr<char> pointerD = pointerC ; //will crash program
	cout << *pointerC << endl ; //will print value it points to

	//
	return 0;
}