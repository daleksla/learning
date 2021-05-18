#include <string>

class Human {
	protected:
		std::string name ;
		int age ;
	public:
		Human(std::string, int) ;
		void printName() ;
		void printAge() ;
		std::string getName() ;
		int getAge() ;
		~Human() ;
};