#include <string>
#include <iostream>
using namespace std ;

/* We can overwrite methods inherited and provide new functionalities */

class Man {
	public :
		void speak() { cout << "Hello!" << endl ; }
		void speak( string msg ) { cout << "    " << msg << endl ; }
};

class Hombre : public Man {
	public :
		void speak( string msg ) { cout << msg << endl ; } //change one of the overload methods
};

int main()
{
  Man henry ;
  Hombre enrique ;

  henry.speak() ;
  henry.speak( "It's a beautiful evening." ) ;

  enrique.speak( "Hola!" ) ;
  enrique.Man::speak( "Es una tarde hermosa." ) ;

  return 0 ;
}