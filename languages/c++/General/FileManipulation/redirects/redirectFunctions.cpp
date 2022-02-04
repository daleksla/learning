#include <iostream>
#include <fstream>
#include <string>
using namespace std ;

/* We can redirect specific stream-methods (such as console out, console error, console log etc.) to text files */

int main() {
    ifstream cin("input.txt");
    ofstream cout("output.txt");

    int a, b;   
    cin >> a >> b;
    cout << a + b << endl;
}