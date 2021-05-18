#include <stdio.h>
using namespace std ;

/* This is my header file containing the class & function declarations
 * They will be implemented in 'kitty.cc' */

class kitty {
 public:
  kitty();
  ~kitty();

  void speak();  
  void speak2(){ printf("totes works\n"); }

 private:
  int variable;

};