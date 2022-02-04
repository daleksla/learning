#include "omp.h"

#include <iostream>
#include <string>

/**
  * @brief File demoing basic openmp usage and how it operates behind the scenes
  * OpenMP works by abstracting away many features of threading.For example, in standard C++, you would have to manually create a `std::thread` for each functionality you wished to perform (technically this is concurrency but whatever). However OpenMP deduces the number of CORES on ones system and runs a given block of code on each core
  * Creating / parallelising:
    * Creating code to run as parallel:
        #pragma omp parallel
            {<code_to_run_parallel_ly>}
    * Creating code to run on specific number of cores: #pragma omp parallel num_threads(x)
                                                        {<code_to_run_parallel_ly>}
        * Note: x is the number of cores to use) allows you manually specific the number of processors to execute said code
    * In both instances, the code to be ran as parallel should be placed within a lexical scope brackets (ie. {})
  */

int main()
{
	#pragma omp parallel // this sets up a call for the region BELOW to be set up as parallel. how this works is that openmp automatically deduces the numbers of cores you have (threads running simultaneously is concurrency, not Parallelism!)
	{ // this lexical scope will serve as the parallel region
		std::cout << "Hi!" << std::endl ; // should be ran once * no. processor your computer has
	}
	std::cout << "Back to serial" << std::endl ; // parallel region ended above
	#pragma omp parallel num_threads(4)
	{
		std::cout << "I should print 4 times, I've been told to!" << std::endl ;
	}

	return 0 ;
}
