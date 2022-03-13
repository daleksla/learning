# mpi

MPI (Message Passing Interface implementation) is a portable messaging passing standard for parallel and distributed computing systems. MPI provides parallel hardware vendors with a clearly defined set of routines which can be efficiently implemented, and is thus optimised for each system. It is available in C/C++ (this repository's language of choice) Fortran, C#, Java and Python, and is a testament to it's high level of portability.

***

To build these files: `mpicxx <filename>.cpp`
  * Note: `mpicxx` is the recommended wrapper around the standard CXX compiler which ensures linkage to MPI specific libraries

To run these files: `mpirun -hostfile <file_containing_node_names> --map-by node <filename>.o <args...>`
  * Notes:
    1. the `mpirun` command can run any executable but MUST be used to run our distributed code
    2. the `hostfile` option should point to a file containing the name of nodes in a given cluster
      * if you don't specify the file containing the nodes it can run on, it will opt to run everything in parallel but limited to running locally (though that might be what you want)
      * On that note, [`pdsh`](https://www.admin-magazine.com/HPC/Articles/pdsh-Parallel-Shell) is a bloody cool parallel shell which can arbitrarily execute commands on multiple machines using SSH (encrypted). I know that it keeps track of the machines on the cluster in `/etc/pdsh/machines/` so one could use that as arguement to the above
    3. `<filename>` represents our binary
    4. `<args...>` represents any command-line arguments the binary above takes
