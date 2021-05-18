#include <iostream>
using namespace std ;

int main() 
	/* Pointer arithmetic - increment pointer value and manipulate values as such */
{
	int nums[] = {1,2,3,4,5,6,7,8,9,10} ; //create int-type array of 10 elements, initialize it
	int* ptr = nums ; //get memory address of (the first element of) the array (no need to use '*')
	//
	for(int i = 0 ; i < 10 ; i+=1) { //loop through array
		cout << "Data at " << ptr << "= " << *ptr << endl ;
		ptr += 1 ; }
	
	ptr += 1 ; //increasing outside the width of the array
	cout << "Data at " << ptr << "= " << *ptr << endl ; //will there4 print a random value in memory
	
	//
	return 0;
}