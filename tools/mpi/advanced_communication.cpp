#include <iostream>
#include <string.h>

#include <mpi.h>

/**
  * @brief File shows how to send complex data constructors over MPI

  * As mentioned in basic_communciation.cpp, MPI uses it's own datatypes as a means to specify the structure of a given message at a higher level
    * Problem with this however is that custom data structures do not fall under this category
    * We can however simply specify the fields a given custom data structure uses and therefore provide MPI with the knowledge how tp perform transformations

  * How to convert structs to MPI types:
    * #1 define number of attributes

    * #2 define array each containing the MPI equivalents of the attributes (in order)

    * #3 define array storing the number of elements of said type of each attribute
        * ie. if you have a standard int attribute, you'd say 1, if it was an array of 5 ints, you would say 5 is the number

    * #4 Determing displacements of each property relative to the start of the container
        * Use MPI_Aint object to store addresses and displacements
        * Use MPI_Get_address(void*, MP_Aint*) to get address of a given pointer
            * void* is a pointer to a given attribute in a class / struct
            * MP_Aint* is a pointer which will be filled with the determined memory address
        * Use the above function to capture address of struct itself and the attributes
        * Then just deduct the address of the struct's start from the'address of each respective property and store each displacement in an array of MP_Aint's

    * #5 Use MPI_Type_create_struct(int, int*, MPI_Aint*, MPI_Datatype* / ompi_datatype_t**, MPI_Datatype* / ompi_datatype_t**)
        * #1 number of attributes
        * #2 array of number of elements of a given type per block
        * #3 array of displacements per property from the start of the struct
        * #4 array of the MPI equivalent datatypes of each attribute
        * #5 pointer to new MPI datatype

    * #6 use MPI_Type_commit(MPI_Datatype* / ompi_datatype_t**) to give MPI information on how to transport data
        * #1 pointer to new MPI datatype calculated from call above

    * #7 return the generated type to be used in program

  */

struct my_data_type {

  char host_name[MPI_MAX_PROCESSOR_NAME] ;

  int id ;

} ;

std::ostream& operator<<(std::ostream& os, const my_data_type& data)
{
    os << "host name: " << data.host_name << ", id: " << data.id ;
    return os ;
}


MPI_Datatype create_mpi_type()
{
    /* Detail type, number of respective elements */
    const int count = 2 ; // how many data types in the struct
    const MPI_Datatype struct_in_types[count] = {MPI_CHAR, MPI_INT} ; // type of every different block of data
    const int len_blocks[count] = {12,1} ; //how many elements per block

    /* Specify starting memory location of each attribute relative to the start of the container */
    my_data_type sbuf ; // make a copy of the struct so we can see where the attribute lie relatively to a given instances start

    MPI_Aint objAddress, address1, address2 ;
    MPI_Get_address(&sbuf, &objAddress) ;
    MPI_Get_address(&sbuf.host_name, &address1) ; // method gets memory address of a var
    MPI_Get_address(&sbuf.id, &address2) ;

    MPI_Aint displacements[count] ;
    displacements[0] = address1 - objAddress ; // to work out where where the first attribute is relatively to the start
    displacements[1] = address2 - objAddress ; // to work out where where the second attribute is relatively to the start

    /* Formalise and publish custom data type to MPI communicator */
    MPI_Datatype mpiHostStruct ; MPI_Type_create_struct(count, len_blocks, displacements, struct_in_types, &mpiHostStruct) ;
    MPI_Type_commit(&mpiHostStruct) ;
    return mpiHostStruct ;
}

int main(int argc, char** argv)
{
    /* Initialisation */
    MPI_Init(&argc, &argv) ;

    /* Main functionality */
    int world_rank ; // process rank in distributed system
    MPI_Comm_rank(MPI_COMM_WORLD, &world_rank) ;

    int world_size ; // number of participating nodes
    MPI_Comm_size(MPI_COMM_WORLD, &world_size) ;

    my_data_type data ;
    MPI_Datatype my_data_type_mpi_type = create_mpi_type() ;

    if(world_rank == 0) // communicator
    {
        int name_len ; MPI_Get_processor_name(data.host_name, &name_len) ;
        data.id = 0 ;
        MPI_Send(&data, 1, my_data_type_mpi_type, 1, 0, MPI_COMM_WORLD) ;
        std::cout << "Data sent from communicator: \"" << data << '\"' << std::endl ;
    }
    else if(world_rank == 1) // child node
    {
        MPI_Recv(&data, 1, my_data_type_mpi_type, 0, 0, MPI_COMM_WORLD, MPI_STATUS_IGNORE) ;
        std::cout << "Process " << world_rank << " received data \"" << data << "\" from communicator node" << std::endl ;
    }

    /* E(nd)O(f)P(rogram) */
    MPI_Finalize() ;
    return 0 ;
}
