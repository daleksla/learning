#include "Python.h"
using namespace std ;

/* Use 'gcc -I/usr/include/python3.5 embeddingexample.cpp -lpython3.5m' to compile */

int main() {
    Py_Initialize();
    PyRun_SimpleString("import sys; sys.path.append('.')");
    PyRun_SimpleString("import embeddingexample;");
    PyRun_SimpleString("print(embeddingexample.myabs(2.0))");
    Py_Finalize();
	//
    return 0;
}

//-l/usr/include/python3