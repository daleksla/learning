#include <algorithm>
#include <iostream>
using namespace std ;

/* We can use templating in classes too, either as return values of methods or as placeholders to it's attributes' 
 * Note: we need to declare upon creating our object what data-type the instance uses 
 * We can create specific instance of class for certain data-types - this is called 'specialisation' */

template<class T>
class Datatype {
	public:
		T data ;
	private:
		Datatype(T input)
		{
			data = input ;
		}
	
		T getData()
		{
			return data ;
		}
} ;

template <> // declare we aren't using templating
class Datatype<std::string> { // here we declare that this class is to be used when strings will be stored
	public:
		std::string data ;
	private:
		Datatype(T input)
		{
			data = input ;
		}
	
		std::string getData()
		{
			return "Hi! " + data ;
		}
} ;
	
int main()
{
	Datatype<int> object1(1) ; // here we declare our class object to be for an int
	Datatype<std::string> object2("peem") ; // this will use our specialised class
	//
	return 0 ;
}