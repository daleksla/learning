#include <fstream>
#include <string>
#include <iostream>
using namespace std ;

int main()
	/* Create string variable, open and add to specific .txt file */
{
	string poem ;
	poem = "\n\tHello!" ;
	poem.append("\n\tI'm Salih"); //use \t to 'tab'
	//
	ofstream writer("poem.txt", ios::app) ; //specify mode (this one is to append). no mode will overwrite
	//if(!writer) {cout << "Error opening file" ;}
	//else {
	writer << poem << endl ;
//}
	writer.close() ;
	//
	return 0 ;
}