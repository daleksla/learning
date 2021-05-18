#include <boost/preprocessor/repetition/repeat.hpp>
#include <iostream>

#define DECL(z, n, text) text ## n = n;

/* This is really confusing but just know that it's a way of re-naming variables based on loops
 * e.g. if you want to create a variable each time you run a loop with a unique name (e.g. name plus iteration no.),
 you can do so using this method */

int main()
{
	BOOST_PP_REPEAT(5, DECL, int a_) ;// expands to int a_0 = 0; int a_1 = 1; ...
	std::cout << a_1 ; //process clearly works, as each variable has a unique name
	std::cout << a_2 ;
	std::cout << a_3 ;
	//
	return 0;
}