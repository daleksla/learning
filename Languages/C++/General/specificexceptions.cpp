#include <stdexcept>
#include <typeinfo>
#include <fstream>
#include <string>
#include <iostream>
using namespace std ;

/* The 'stdexcept' library allow us to create specific exceptions based on certain errors
	 * e.g. catch(out_of_range &e)
 * We can use the 'typeinfo' library during program creation to inform us of the errors we should make exceptions for
	 * e.g. out_of_range, length_error etc.
 * Use these throughout your program to ensure the program doesn't unexpectantly terminate AND to deal with each issue seperately */ 

int main()
{
	string language = "C++" ;
	int num = 10000 ;
	try 
	{ language.erase(100,200); } //destined to fail as we have not got 100 characters
	catch(out_of_range &e) 
	{
		cout << "Meow" << endl ; //specific error
	} 
	catch(exception &e) //general error, won't run as catch above works
	{
		cout << "Exception type: " << typeid(e).name() << endl ; //provides us with the error type's name
		cout << "Woof" << endl ;
	} 
	//
	return 0 ;
}