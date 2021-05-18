#include <cctype>
#include <fstream>
#include <iostream>
using namespace std ;

int main()
{
    ifstream file("./a.out", ios::binary);

    char c;
    while(file.get(c)) // don't loop on EOF
    {
        if(isprint(c)) // check if is printable
		{
            cout << c ;
		}
    }
	cout << "\n" << endl ;
	//
	return 0 ;
}