#include <cstdio>
#include <iostream>
using namespace std;

/* We can direct all methods, such as anything to print to the standard output (stdout) to text files */

int main()
{
    freopen("output.txt","w",stdout);
    cout<<"write in file";
    return 0;
}