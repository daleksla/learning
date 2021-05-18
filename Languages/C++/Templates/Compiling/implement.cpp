#include "header.hpp"
#include <algorithm>
#include <string>
#include <iostream>

/* In this file, we will implement the class methods / functions we defined in 'header.hpp' */

template <class T> //just like declaration + implementations at once, we declare each time the 'typename'
Person<T>::Person(T inputName, int inputAge)
{
	name = inputName ;
}

template <class T>
T Person<T>::getName()
{
	return name ;
}

template <class T> 
int Person<T>::getAge()
{
   return age ;
}

// Below is really the major difference - we need to declare the possible instances of 'T'
// Here we declare the possible values our class can take - and the copies therefore it'll generate
template class Person<char*> ; //create a class template using char* / c-string
template class Person<std::string> ; //create a class template using std::string