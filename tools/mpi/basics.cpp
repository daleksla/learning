#include <iostream>

#include <mpi.h>

/**
  * @brief File demonstrating basic skeleton of programs using MPI

  * MPI_Init(int*, char**) creates all MPI's global and internal variables
    * #1 &argc
    * #2 &argv to provide environmental information
    * If you don't care, assign NULL to both
    * One such variable created by former function is MPI_COMM_WORLD which is a default communicator object

  * MPI_Comm_size(MPI_Comm, int*) - determines the size of the group associated with a communicator
    * #1 communicator / handle object
    * #2 pointer to int to store result

  * MPI_Comm_rank(MPI_Comm, int*) - determines the rank of the calling process in the communicator
    * #1 communicator / handle object
    #2 pointer to int to store results

  * MPI_Get_processor_name(char*, int*) - provides unique specifier for the actual (as opposed to virtual) node
    * #1 array of at least MPI_MAX_PROCESSOR_NAME (MPI value) characters
    #2 length of character in the given name

  * MPI_Finalize() - terminates MPI execution environment
    * It is suggested to simply return and exit after this point as opposed to perform heavy computation

  */

int main(int argc, char** argv)
{
    MPI_Init(nullptr, nullptr) ; // initialise the MPI environment

    /* Get number of nodes also in world  */
    int world_size ;
    MPI_Comm_size(MPI_COMM_WORLD, &world_size) ;

    /* Get rank of processing node */
    int world_rank ;
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank) ;

    /* Get name of current processing node */
    char processor_name[MPI_MAX_PROCESSOR_NAME] ; // assign relevant memory
    int name_len ;
    MPI_Get_processor_name(processor_name, &name_len);

    // Print off a hello world message
    std::cout << "Hello world from processor " << processor_name << ". Rank " << world_rank << " out of " << world_size << " processors" << std::endl ;

    // E(nd)O(f)P(rogram)
    MPI_Finalize() ; // Finalize the MPI environment
    return 0 ;
}
