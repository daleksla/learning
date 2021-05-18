#include <string>
#include <iostream>
#include "example.h"

Human::Human(std::string i_name, int i_age)
{
	this->name = i_name ;
	this->age = i_age ;
}

void Human::printName()
{
	std::cout << name << "\n" ;
}

void Human::printAge()
{
	std::cout << age << "\n" ;
}

std::string Human::getName()
{
	return name ;
}

int Human::getAge()
{
	return age ;
}

Human::~Human()
{
	std::cout << "Object Destroyed!\n" ;
}
