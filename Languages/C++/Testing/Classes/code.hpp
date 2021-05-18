#include <iostream>
#include <string>
#include <vector>
using namespace std ;

class Human {
	protected:
		string name ;
		int age ;
		vector <int> dob ;
		string cyob, cnob ;
	public:
		Human(string, int, vector <int>, string, string) ;
		~Human() ;
		int getDay() ; 
		int getMonth() ; 
		int getYear() ;
		string getName() ;
		string getCyob() ;
		string getCnob() ;
		int getAge() ;
		string formatDob() ;
};