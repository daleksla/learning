/* This is our interface file, where we declare our 'module' (to be in Python)
 * It contains either:
	 * Independant declarations for each function
	 * Header file containing declarations (opt for the latter)
 * To run the necessary commands to make our module availible, look at 'Makefile'
 */

%module kitty
%{
  #include "kitty.hpp"
%}

%include "kitty.hpp"