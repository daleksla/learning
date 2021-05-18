#include "../General/input.h"
#include <iostream>
#include <sstream>
#include <string>
#include <stdexcept>
#include <memory>

/* Vectors are typically the way to go regarding dynamic lists in C++
 * However sometimes this isn't an option & using pointers allow for us to create dynamic lists */

int task()
{
	int size = 0;

	// get the size
	while( size <= 0 )
	{
		std::cout << "Enter a size: ";
		try
		{
			size = input<int>(); // using my function for getting input
		}
		catch( std::runtime_error &e )
		{
			std::cerr << "Not an integer" << std::endl;
		}
	}

	std::cout << "Reading in " << size << " values." << std::endl;

    // read in the values
	int *values = new int[size]; //this is called dynamically allocated memory
	//we basically took the size needed then created an integer list called values
	//think of an array as pointing to memory, therefore the pointer type is required

	for( int i=0; i<size; ++i )
	{
		while(true)
		{
			std::cout << "Enter a value: ";
			try
			{
				values[i] = input<int>();
				break;
			}
			catch( std::runtime_error &e )
			{
				std::cerr << "Not an integer" << std::endl;
			}
		}
	}	

    // print everything in reverse
	for( int i=size-1; i>=0; --i )
	{
		std::cout << "Element " << i << " is " << values[i] << std::endl;
	}

    delete [] values; //to delete a pointer array

	return 0;
}