#include <string>
#include <iostream>
using namespace std ;

/* Classes can have built in functions run from the moment an instance is created. This is called a 'constructor'
 * A destructor is used automatically the moment code has run it's course.
 * Both have the name of the class. Class() = Constructor, ~Class() = Destructor */

class Dog {
	private:
		int age, weight ;
		string colour ;
	public:
		Dog(int age, int weight, string colour) {this->age=age ; this->weight=weight ; this->colour=colour ;} //constructor
		~Dog() {"Object is destroyed" ;} //destructor
		void bark() {cout << "Woof" << endl ;}
		void setValues(int, int, string) ;
		void setAge(int inputted_age) {this->age = inputted_age ;} //'this->' makes us look at the variable within the class of said name
		void setWeight( int lbs ) { weight = lbs ; }
		void setColour( string hue ) { colour = hue ; }   
		int getAge() { return age; }
		int getWeight() { return weight; }
		string getColour() { return colour; }
} ;

int main()
{
	Dog fido(3, 15, "brown") ;
	//fido.setValues(3, 15, "brown") ;
	
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