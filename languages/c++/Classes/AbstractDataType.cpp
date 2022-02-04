#include <iostream>
using namespace std ;

/* An 'Abstract Data Type' is essentially fancy talk for another class
 * However they typically are a concept, rather than a class we typically create instances of
 * They typically contain pure virtual methods and are inherited and modified (type of capability class) */

class Shape {
	public:
		virtual int getArea() = 0;
		virtual int getEdge() = 0;
		virtual void draw() = 0;
};

class Quadrilateral : public Shape {
	private:
	
		int width, height ;
	
	public:
	
		Quadrilateral(int width, int height) 
		{
			this->width=width;
			this->height=height;
		};
		~Quadrilateral() ;
			
		int getArea() {return height * width ;}
	
		int getEdge() {return (2*height)+(2*height) ;}
	
		void draw() 
		{
			for(int y=0 ; y < height ; y++) 
			{
				for(int x=0 ; x < width ; x++) 
				{
					cout << "x " ;
				}
				cout << endl ;
			}
		}
};

int main()
{
	//declare new instance to the class and save it directly into a pointer
	Shape* square = new Quadrilateral(5,5) ;
	Shape* rectangle = new Quadrilateral(3,7) ;
	//note:despite the fact it's stored as a pointer to 'Shape', it can use the functionality declared as 'virtual' in base class
	square-> draw() ; 
	cout << endl ;
	rectangle-> draw() ;
	//
	return 0 ;
}