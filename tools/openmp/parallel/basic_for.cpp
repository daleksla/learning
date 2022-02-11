#include "omp.h"

#include <iostream>
#include <string>

/**
  * @brief File demoing openmp usage when using for loops and how it operates behind the scenes
    * Note: this file is only relevant to show a shorthand way to easily convert a sequential for loop into parallel code. If you genuinely want each thread to run several iterations, ignore this and see 'hello_omp.cpp'
  * OpenMP makes use of a threadpool to execute for loops - it automatically creates a thread for each processor a host system has or as many threads as the for loop mandates (whichever is smaller) and executes each iteration of the for loop in parallel.
    * Note: the number of iterations must be known at COMPILE time - this is because OPENMP operates as a compile time library and unrolls the code it needs for a program to run at that time
    * For an iteration which has not been assigned a thread, it simply awaits till an iteration running on a thread has finished, upon which it seizes its thread and runs its own functionality.
    * Benefit of a threadpool involves not constantly creating and deleting threads, which is costly
    * Note: For loops in OpenMP can take many more parameters (see variables.cpp, schedueling.cpp)
  */

int main()
{
	#pragma omp parallel for // this sets up a call for the region BELOW to be set up as a for loop to run in parallel - it creates a threadpool filled with one thread * many cores you have. from this, each thread is allocated to an element of the for loop. if it isnt assigned a thread originally, that specific iteration waits till a thread has finished executing, then takes it over to run its own stuff
	for(int i = 0 ; i < 32 ; ++i) // note: since openmp is a compile-time library, you MUST have all this information statically available (ie 32 can not be determined from a variable)
	{ // this lexical scope will once again serve as the parallel region
		std::cout << i << std::endl ; // should be ran once * no. processor your computer has. note: due to the nature of OS-determined sequencing, it WON't be in order.
	}
	std::cout << "Back to serial" << std::endl ; // parallel region ended above
	return 0 ;
}
