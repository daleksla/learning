#include <iostream>
#include <string>
using namespace std ;

int main()
	/* Create variables, point to memory & manipulate */
{
	int num = 100 ; //create variable
	float sum = num + .101010 ;
	string text = "Hello Salih!" ;
	//
	cout << "Integer variable starts at: " << &num << endl ; //print location
	cout << "Float variable starts at: " << &sum << endl ;
	cout << "String variable starts at: " << &text << endl ;
	//
	int* numPointer = &num ; //create pointer & save it
	float* sumPointer = &sum ;
	string* textPointer = &text ;
	//
	cout << "num = " << *numPointer << endl ; //dereference pointer (get content)
	cout << "sum = " << *sumPointer << endl ; 
	cout << "text = " << *textPointer << endl ; 
	
	int* anotherIntPointer = NULL ;//pointers can be assigned as NULL (e.g. to be used later)
	//
	return 0;
}