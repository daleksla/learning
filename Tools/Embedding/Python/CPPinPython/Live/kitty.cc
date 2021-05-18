#include <stdio.h>
#include "kitty.hpp"
using namespace std ;

/* This file contains code implementation for 'kitty.hpp' */ 

kitty::kitty(){
  printf("Constructor\n");
  variable = 100;
}

kitty::~kitty(){
  printf("Destructor\n");
  variable = 0;
}

void kitty::speak(){
  printf("I'm a cat.\n");
}