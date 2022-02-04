#include <map>
#include <vector>
#include <algorithm>
#include <iterator>
#include <iostream>
#include <string>
using namespace std ;

/* Maps are the dictionary-like structure in C++
 * Each entry contains a 'key' & 'value' - you need the key you will need this to access the value
 * This program highlights how to create, insert & retrieve values from Maps */

int main()
{
	map<int, char> second; //normal, 2D map
	second.insert( pair<char,int>(1, 'a') ); //this will insert value into our map
	cout << second[1] << endl ; //print the value pair for key '1'
	//
	map<int,map<string, char> > first; //this is a 3D map
	first[1].insert(make_pair("Peter Q.", 'a')); //this is how to insert values into all the spaces
	cout << first[1]["Peter Q."] << endl ; //this is how to access key values
	
	// showing contents in a loop
	for(auto it = second.cbegin(); it != second.cend(); ++it) 
	{
		cout << "{" << (*it).first << ": " << (*it).second << "}\n";
	}
	//
	return 0 ;
}