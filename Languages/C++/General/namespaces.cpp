#include <string>
#include <iostream>
using namespace std ;

/* Namespaces allow us to group named entities that otherwise would have global scope into narrower scopes, giving them namespace scope. 
 * This allows organizing the elements of programs into different logical scopes referred to by names.
 * A namespace is a declarative region that 'provides a scope to the identifiers' (names of the types, function, variables etc) inside it.
 * Multiple namespace blocks with the same name are allowed. 
 * All declarations within those blocks are declared in the named scope.
 * All items in different namespaces must be prefix'd by '<namespace-name>::<item-name>' 
	 * with exception to those part from those in the std namespace
 * Note: Namespace is a feature added in C++ and not present in C. */

namespace seperate //create a new namespace
{
    string name = "Salih" ; //content of said namespace
} 

int main()
{
	cout << "Hello " << seperate::name << endl ; //first:: is needed as a prefix to address the name variable from it
	int age = 10 ;
	cout << "Age: " << age << endl ;
	return 0 ;
}