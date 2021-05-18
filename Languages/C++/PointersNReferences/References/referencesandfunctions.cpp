#include <iostream>
using namespace std ;

/* How to pass references to functions & how to manipulate data further 
 * note it's similarity to 'pointersandfunctions.cpp' - we merely replace pointers w/ references 
 * also as a side point ; declaring 'prototype' functions allows for you to have functions in any order*/

void printValue(int&) ; //can be filled in later
void changeValue(int&) ;

int main()
{
	int num = 5 ;
	int& numReference = num ;
	//
	printValue(numReference);
	changeValue(numReference);
	printValue(numReference);
	//
	return 0;
}

void printValue( int& value )
{
  cout << "Current value: " << value << endl ;
}

void changeValue( int& value)
{
  value *= 3 ;
}