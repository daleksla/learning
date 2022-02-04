#include <iostream>
#include <string>
using namespace std ;

/* Inheritance is a concept, where a class may inherit select properties of another */

class Polygon { //'parent' class
	protected: //acts as private but can be inherited
		int width, height ;
	public:
		void setValues(int width, int height) {this->width=width ; this->height=height ;}
		virtual int area () = 0; //virtual functions are idle but ensure child class' have a method with this name 
};

class Rectangle : public Polygon {
	public:
		int area() {return (width * height); } //here we create the actual method with the same name
};

class Triangle : public Polygon {
	public:
		int area() {return (width * height)/2; }
} ;

int main()
{
	Rectangle rectangle ; 
	rectangle.setValues(4,5) ;
	Triangle triangle ;
	triangle.setValues(4,5) ;
	cout << "Rectangle's area = " << rectangle.area() << endl ;
	cout << "Triangle's area = " << triangle.area() << endl ;
	//
	return 0 ;
}
