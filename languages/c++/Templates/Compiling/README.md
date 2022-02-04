# Compilation when using templates

## Implementation and declaration together
If this is the case, the examples in ../Basics.cpp and ../Class.cpp should suffice - other than defining them, no other work is needed
That being said, this approach will be very bulky if it's within a header file and is not optimum for compilation

## Separating the implementation, declaration
Ideally, this is what should be done when programming in C++, especially if you then wish to go on to create libraries
However, it should be noted that doing so tends to cause code bloating (due to defining so many templates as the compiler cannot deduce 'needed' ones)
Furthermore, it'll only use the template to generate class models you explicitly declare
* In the file 'header.hpp', I will define a few basic functions with template names
* In the file 'implement.cpp', I will implement these definitions