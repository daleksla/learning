#include <string>
#include <iostream> 
using namespace std ;

/* Classes are data strcuctures that can store variables and functions in a single entity 
 * A class typically reflects a real life object (e.g. Animal, Car)
 * A class can shield itself from outside intererences using 'access specifiers'
	 * Public - can be accessed anywhere
	 * Private - only things in the class can use them ; the default
	 * Protected - same as private except class' inheriting */  

class Dog {
	private:
		int age, weight ;
		string colour ;
	public:
		void bark() {cout << "Woof" << endl ;}
		void setAge(int inputted_age) {this->age = inputted_age ;} //'this->' makes us look at the variable within the class of said name
		void setWeight( int lbs ) { weight = lbs ; }
		void setColour( string hue ) { colour = hue ; }
    
		int getAge() { return age; }
		int getWeight() { return weight; }
		string getColour() { return colour; }
} ;

int main()
{
  Dog fido ;

  fido.setAge( 3 ) ;
  fido.setWeight( 15 ) ;
  fido.setColour( "brown" ) ;

  cout << "Fido is a " << fido.getColour() << " dog" << endl ;
  cout << "Fido is " << fido.getAge() << " years old" << endl ;
  cout << "Fido weighs " << fido.getWeight() << " pounds" << endl ;

  fido.bark() ;

}