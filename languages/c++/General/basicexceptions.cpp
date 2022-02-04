#include <string>
#include <stdexcept>
#include <iostream>
using namespace std;

/* A programmer can assume certain errors will occur during his program (esp. run-time errors)
 * Exception Handling allows us to 'solve' our errors either generally based on the error 
	 * By general we mean if an error occurs, regardless of the type
	 * We will go into specific error handling in 'specificexceptions.cpp' 
 * Use these throughout your program to ensure the program doesn't unexpectantly terminate */

int main()
{
	string lang = "C++";
	try 
	{
		lang.erase(0,3) ;} //remove character's with index 0-2
	catch(exception&error) 
	{
		cout << "Exception: " << error.what() << endl ;
	} //will run if 'try' fails (it won't)
	try {lang.erase(5,10000) ;} //will fail due to lack of presence of a 5th character
	catch(exception&error) {cout << "Exception: " << error.what() << endl ;} //will run if 'try' fails (it will)
	//
	return 0;
}