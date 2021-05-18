cmake_minimum_required(VERSION 2.8) # using at least version 2.8 of CMake
set(CMAKE_CXX_STANDARD 14) # using C++14
project(cmake_example CXX)

# location of source code files
include_directories(${CMAKE_SOURCE_DIR})

# tell cmake where to put the executables that it creates
file(MAKE_DIRECTORY ${CMAKE_SOURCE_DIR}/.) # deposit it in current directory
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_SOURCE_DIR}/. )
#if u put another folder name it'd put it there / would create a folder if needed

# where to put the object files it creates
file(MAKE_DIRECTORY ${CMAKE_SOURCE_DIR}/lib) # make a folder called lib
SET(LIBRARY_OUTPUT_PATH ${CMAKE_SOURCE_DIR}/lib)

# files we actually want to compile
add_library( example example.cpp ) #other .cpp files (note: if there was more then one file, it would make each an object (.o) then links them into a library)
add_executable( sourceexample sourceexample.cpp ) # file with our main function in it
target_link_libraries( sourceexample example ) #recompiles our library object with our source object

#result: executable called sourceexample.o will be stored in a folder in current directory