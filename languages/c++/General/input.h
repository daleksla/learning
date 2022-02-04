#ifndef INPUT_H
#define INPUT_H

#include <stdexcept>
#include <limits>
#include <iostream>

/* Getting input from the user in C++ is simply a matter
    of saying:
        int value;
        std::cin >> value;
    However, getting C++ to handle invalid input is 
    surprisingly complex. So here is a input() function
    that I have written that does it all for you.
    It behaves in a similar way to input() in Python
    and will raise a runtime_error exception if the user
    trys to enter anything that can't be converted to the
    correct type. You don't need to know how this work at
    the moment, just type...
        
        int value = input<int>();

    ... to read in ints or ...
        
        float value = input<float>();

    ..if you watch to read floats etc. . */
template<typename T>
T input()
{
    T value;
    std::cin >> value;

    if( std::cin.fail() )
    {
        std::cin.clear();
        std::cin.ignore( std::numeric_limits<std::streamsize>::max(), '\n' );
        throw std::runtime_error("Input is of invalid type");
    }

    return value;    
}

#endif