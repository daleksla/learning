# OpenMP

OpenMP is an library used to support the creation of programs featuring shared memory & multiprocessor usage. It is a library available in C, C++, Fortran & Matlab. It is an abstract library, allowing, via minimally invasive `#pragma` statements, to add parallelism to existing source code (ie. turns for-loops into programs where each iteration is ran in parallel on a given core, etc.).

***

The files in this subfolder show the basics of how to use parallel programming and examples of what it should output. To compile these files: `g++ --std=c++2a <file_name>.cpp -fopenmp -lgomp`
