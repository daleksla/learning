#include <iostream>
#include <string>
#include <vector>
using namespace std ;

float func()
{
	
return 10 / 0 ;
}

int main() 
{
	bool x ;
	x = true ;
	cout << func() << endl ;
	return func() ;
	//
	return 0 ;
}