#include <algorithm>
#include <string>

/* This file contains a class which makes use templating
 * We will only declare a class here
 * We will then implement the functionality in 'implement.cpp' 
 * Note: this functionality doesn't work with regular functions! */

template <class T> 
class Person {
	private:
		T name ; // placeholder for a std::string or  c-style string (char* / char[]) 
		int age ;
	public:
		Person(T, int) ;
		T getName() ;
		int getAge() ;
} ;