#include <iostream>
#include <string>
using namespace std ;

/* Inheritance is a concept, where a class may inherit select properties of another
 * You can inherit the constructors of one class (methods used after an object is declared */

class Polygon { //'parent' class
	protected: //acts as private but can be inherited
		int width, height ;
	public:
		Polygon(int width, int height) {this->width=width ; this->height=height ;}
};

class Rectangle : public Polygon {
	public:
		Rectangle(int width, int height) : Polygon(width, height) {}; //create constructor that uses parent
		int area() {return (width * height); } //here we create the actual method with the same name
};

class Triangle : public Polygon {
	public:
		Triangle(int width, int height) : Polygon(width, height) {} ;
		int area() {return (width * height)/2; }
} ;

int main()
{
	Rectangle rectangle(4,5) ;
	Triangle triangle(4,5) ;
	cout << "Rectangle's area = " << rectangle.area() << endl ;
	cout << "Triangle's area = " << triangle.area() << endl ;
	//
	return 0 ;
}
