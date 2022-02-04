#include <string>
#include <vector>
#include <iostream>
#include <algorithm> // templates in here!
using namespace std ;

/* Templates are a good way to implement generic functions for multiple data-types
 * For example, the '+' function / operator works for any numerical datatype
 * Equally, we can then go on to overload the function for specific data-types 
 * Note: you cannot declare a template and implement later - you MUST do both at once
	 * Well technically you can - but involves you declaring all possible instance the function may possess
	 * That is called 'explicit instantination' */

template<typename T> 
void times(T a, T b) //if both inputs are of the same type
{
	cout << a * b << endl ;
}

// There is two ways we can write for specific parameter types of a function
void times(std::string a, int b)  //specific overload example, otherwise above is called
{
  std::string returnValue = "";
  for(int counter = 0; counter < b ; counter+=1) {returnValue += a ;}
  cout << returnValue << endl ;
}

int main()
{
	times(1.2f , 33838.3f) ;
	times("s", 5) ;
	//
	return 0 ;
}