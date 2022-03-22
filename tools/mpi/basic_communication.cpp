#include <iostream>

#include <mpi.h>

/**
  * @brief File shows how to send basic data constructors over MPI

  * MPI uses it's own datatypes as a means to specify the structure of a given message at a higher level
    * 13 types:
        * (signed) char            -->    MPI_BYTE
        * unsigned char            -->    MPI_UNSIGNED_CHAR
        * (signed) short int       -->    MPI_SHORT
        * unsigned short int       -->    MPI_UNSIGNED_SHORT
        * (signed) int             -->    MPI_INT
        * unsigned int             -->    MPI_UNSIGNED
        * (signed) long int        -->    MPI_LONG
        * unsigned long int        -->    MPI_UNSIGNED_LONG
        * (signed) long long int   -->    MPI_LONG_LONG
        * unsigned long long int   -->    MPI_UNSIGNED_LONG_LONG
        * float                    -->    MPI_FLOAT
        * double                   -->    MPI_DOUBLE
        * long double              -->    MPI_LONG_DOUBLE
    * You need to specify what datatype is being sent / received and MPI will do the conversions behind the scenes for you
    * Note: see `complex_communication.cpp` for creating your own MPI types for communication purposes

    * MPI_Send(void*, int, MPI_Datatype, int, int, MPI_Comm) - sends data to a specified destination
      * #1 is pointer to start of data
      * #2 is length of data
      * #3 is corresponding MPI datatype
      * #4 is rank number (see basics.cpp) of destination node
      * #5 is tag (Tags are an arbitrary way to identify types of messages such that a receiving process can use these tags to decide what messages it wants to receive at a given time)

    * MPI_Recv(void*, int, MPI_Datatype, int, int, MPI_Comm, MPI_Status*) - sends data to a specified destination
      * fields #1-#5 are the same as MPI_Send
      * #6 is a pointer to MPI status of a reception operation (ie. how the receiving call blocks process till message comes in, etc.)
        * Will return one of the following:
            * MPI_Wait
            * MPI_Waitall
            * MPI_Waitany
            * MPI_Waitsome
        * Pass MPI_STATUS_IGNORE if you don't care
  */


int main(int argc, char** argv)
{
    /* Initialisation */
    MPI_Init(&argc, &argv) ;

    /* Main functionality */
    int world_rank ; // process rank in distributed system
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank) ;

    int world_size ; // number of participating nodes
    MPI_Comm_size(MPI_COMM_WORLD, &world_size) ;

    int number ;
    if(world_rank == 0) // communicator
    {
        number = -1 ;
        std::cout << "Communicator sending value " << number << "to nodes" << std::endl ;
        MPI_Send(&number, 1, MPI_INT, 1, 0, MPI_COMM_WORLD) ; // send one item of data to node rank 1
    }
    else if(world_rank == 1) // child node
    {
        MPI_Recv(&number, 1, MPI_INT, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE) ; // receive one item of data from node rank 0 (head / communicator)
        std::cout << "Process " << world_rank << " received number " << number << " from communicator node" << std::endl ;
    }

    /* E(nd)O(f)P(rogram) */
    MPI_Finalize() ;
    return 0 ;
}
