#include <string>
#include <iostream> 
using namespace std ;

/* You can use classes as a template - 'objects' are instances of class. You can have multiple objects */  

class Dog {
	private:
		int age, weight ;
		string colour ;
	public:
		void bark() {cout << "Woof" << endl ;}
		void setValues(int, int, string) ;
		void setAge(int inputted_age) {this->age = inputted_age ;} //'this->' makes us look at the variable within the class of said name
		void setWeight( int lbs ) { weight = lbs ; }
		void setColour( string hue ) { colour = hue ; }
    
		int getAge() { return age; }
		int getWeight() { return weight; }
		string getColour() { return colour; }
} ;

void Dog::setValues( int age, int weight, string colour ) // initializng a class function OUTSIDE the class (only possible after declaring it from within the class)
{
  this -> age = age ;
  this -> weight = weight ;
  this -> colour = colour ;
}


int main()
{
	Dog fido ;
	fido.setValues(3, 15, "brown") ;
	//   fido.setAge( 3 ) ; //replaced with a function to set multiple methods
	//   fido.setWeight( 15 ) ;
	//   fido.setColour( "brown" ) ;
	
	cout << "Fido is a " << fido.getColour() << " dog" << endl ;
	cout << "Fido is " << fido.getAge() << " years old" << endl ;
	cout << "Fido weighs " << fido.getWeight() << " pounds" << endl ;
	fido.bark() ;
	
	Dog pooch ;
	pooch.setValues(4, 18, "grey") ;
	
	cout << "Pooch is a " << pooch.getColour() << " dog" << endl ;
	cout << "Pooch is " << pooch.getAge() << " years old" << endl ;
	cout << "Pooch weighs " << pooch.getWeight() << " pounds" << endl ;
	pooch.bark() ;

}