#include <iostream>

#include <mpi.h>

/**
  * @brief File demonstrating basic skeleton of programs using MPI
  * MPI_Init() creates all MPI's global and internal variables
  */

int main(int argc, char** argv)
{
    MPI_Init(nullptr, nullptr) ; // initialise the MPI environment

    int world_size ; // Get the number of processes
    MPI_Comm_size(MPI_COMM_WORLD, &world_size) ;

    int world_rank ; // Get the rank of the process
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank) ;

    char processor_name[MPI_MAX_PROCESSOR_NAME] ; // Get the name of the processor
    int name_len ;
    MPI_Get_processor_name(processor_name, &name_len);

    // Print off a hello world message
    std::cout << "Hello world from processor " << processor_name << ". Rank " << world_rank << " out of " << world_size << " processors" << std::endl ;

    // E(nd)O(f)P(rogram)
    MPI_Finalize() ; // Finalize the MPI environment
    return 0 ;
}
