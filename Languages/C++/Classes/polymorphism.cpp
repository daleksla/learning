#include <iostream>
#include <string>
#include <vector>
using namespace std ;

/* This program demonstrates 'Polymorphism'
 * In this program you can see we have a base & two child classes
 * We can reference either of the two children using the Base class (ie. using pointers)
* This allows us to access the base class properties (ONLY) of either class DESPITE them having their own additional properties)!
 * However, suppose two of them will have a method with the same name but the functionality inside is different, yet we want to access it using a reference to the base class?
 	* One solution would be to implement a function in the base class, however like I said, the functionality for each class afterwards is different
		* And yes, whilst we can overwrite the base class method later, referencing it using a pointer to the parent class will simply call the parent class method (which we said would be different)
 	* Instead, We can create a 'virtual' method - this is a just a placeholder
		* This method MUST be implemented in the child class
		* We can then reference the object using the parent class pointer & it will call the child class definition of what that function should be
*/

//here i make my classes

class Humanoid {
	private:
		string name ;
		int age ;
		const vector<int> dateOfBirth ;
	public:
		Humanoid(string i_name, int i_age, vector<int> i_dateOfBirth) : dateOfBirth(i_dateOfBirth)
		{
			this->name = i_name ;
			this->age  = i_age ;
		}

		string getName() {return name ;}

		int getAge() {return age ;}

		vector<int> getDateOfBirth() {return dateOfBirth ;}

		virtual void speak() = 0 ;
};

class Human : public Humanoid {
	private:
		const string mother, father ;
		vector<string> children ;
	public:
		Human(string i_name, int i_age, vector<int> i_dateOfBirth, string i_mother, string i_father, vector<string> i_children) : Humanoid(i_name, i_age, i_dateOfBirth) , mother(i_mother), father(i_father)
		{
			this->children = i_children ;
		}

		Human(string i_name, int i_age, vector<int> i_dateOfBirth, string i_mother, string i_father) : Humanoid(i_name, i_age, i_dateOfBirth) , mother(i_mother), father(i_father)
		{
			this->children  = {} ;
		}

		string getMother() {return mother ;}

		string getFather() {return father ;}

		vector<string> getChildren() {return children ;}

		void speak() {cout << "Good day!" << endl ;}
};

class Robot : public Humanoid {
	private:
		string mission ;
		const string maker ;
	public:
		Robot(string i_name, int i_age, vector<int> i_dateOfBirth, string i_mission, string i_maker) : Humanoid(i_name, i_age, i_dateOfBirth), maker(i_maker)
		{
			this->mission = i_mission ;
		}

		string getMission() {return mission ;}

		string getMaker() {return maker ;}

		void speak() {cout << "I WILL EXECUTE MY MISSION" << endl ;}
};

//here will define my classes & access them using a pointer to the base class

int main() 
{
	Human Salih("Salih", 20, {8, 12, 2000}, "Baba", "Mama") ;
	Robot Enoch("Enoch", 32000, {8, 12, 2000}, "Anthropologist", "Salih") ;
	
	Humanoid* pointerToSalih = &Salih ; //create a pointer to Human object as Humanoid - will point to properties they share / that were inherited 
	Humanoid* pointerToEnoch = &Enoch ; //""
	
	cout << pointerToSalih->getName() << endl ; //this calls getName() function - since it's defined in the base class we can use it
	cout << pointerToEnoch->getAge() << endl ; //again, the getAge() function was defined in the base class
	
	//cout << pointerToEnoch->getMission() << endl ; //this line will FAIL as the getMission() function was declared in the child class ONLY 
	
	pointerToSalih->speak() ; // it's declared in the parent class as a virtual function which allows the implementation in each derived class to become the functionality even when pointing at the base class properties only, hence the output of this code will be different to below
	pointerToEnoch->speak() ;
	//
	return 0 ;
}