#include <iostream>
#include <string>
#include <vector>
#include "code.hpp"
using namespace std ;

Human::Human(string i_name, int i_age, vector <int> i_dob, string i_cyob, string i_cnob)
{
	this->name = i_name ;
	this->age = i_age ;
	this->dob = i_dob ;
	this->cyob = i_cyob ;
	this->cnob = i_cnob ;
}

Human::~Human()
{
	cout << "Object Destroyed!\n" ;
}

string Human::getName() 
{
	return name ;
}

int Human::getDay()
{
	return dob[0] ;
}

int Human::getMonth()
{
	return dob[1] ;
}

int Human::getYear()
{
	return dob[2] ;
}

string Human::getCyob()
{
	return cyob ;
}

string Human::getCnob()
{
	return cnob ;
}

int Human::getAge()
{
	return age ;
}

string Human::formatDob()
{
	string temp = to_string(dob[0]) + "/" + to_string(dob[1]) + "/" + to_string(dob[2]) ;
	return temp ;
}