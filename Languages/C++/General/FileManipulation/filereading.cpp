#include <fstream>
#include <string>
#include <iostream>
using namespace std ;

int main()
	/* Open text file, each line to a variable & print it */
{
	ifstream reader("poem.txt") ; //to open file to read
	string line ; //set up variable to store each line

	for(int i = 0 ; ! reader.eof() ; i+=1 ) //go through each line until there's nothing left
	{
		getline(reader, line); //get data on each line
		cout << line << endl ; //print each line on new line
		//cout << i << endl ;
	}
	//
	return 0 ;
}