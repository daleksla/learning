#include <string>
#include <iostream>
using namespace std ;

/* Using functional and object-oriented programming, specifically passing the objects between, poses a difficulty
 * As you pass an object to a function it will pass the function a local copy - this means modifications of said item is a challenge
 * However, using pointers, we can edit the memory address (and therefore the content of the variable) directly! 
 * This also means we don't need to passback an updated copy of the object to the function it was called from */

class Human {
	protected:
		string forename ; string surname ;
		string* pointerToForename ; string* pointerToSurname ;

		int age ; int* pointerToAge ;
	
		int day, month, year ;
		int* pointerToDay ; int* pointerToMonth ; int* pointerToYear ;
	
		string city, country ;
		string* pointerToCity ; string* pointerToCountry ;
	
	public:
	
		Human(string i_forename, string i_surame, int i_age, int i_day, int i_month, int i_year, string i_city, string i_country)
		{
			this->forename = i_forename ; this->pointerToForename = &forename ;
			this->surname = i_surname ; this->pointerToSurname = &surname ;
			this->age = i_age ; this->pointerToAge = &Age ;
			this->day = i_day ; this->pointerToDay = &day ;
			this->month = i_month ; this->pointerToMonth = &month ;	
			this->year = i_year ; this->pointerToYear = &year ;
			this->city = i_city ; this->pointerToCity = &city ;
			this->country = i_country ; this->pointerToCountry = &country ;
			cout << "Object created!\n" ;
		}
	
		~Human()
		{
			cout << "Object destroyed!\n" ;
		}
	
		string* getForename()
		{
			return &pointerToForename ;
		}
	
		string* getSurname()
		{
			return &pointerToSurname ;
		}
	
		int* getDay()
		{
			return pointerToDay ;
		}

		int* getMonth()
		{
			return pointerToMonth ;
		}
	
		int* getYear()
		{
			return pointerToYear ;
		}
	
		string* getCity()
		{
			return pointerToCity ;
		}
	
		string* getCountry()
		{
			return pointerToCountry ;
		}
};

void changerFunction(Human human)
{
	//in this function if we change the values, we haven't a need to return the object copy
}

int main()
{
	Human human("Salih", "Ahmed", 19, 8, 12, 2000, "Birmingham", "United Kingdom") ;
	changerFunction(human) ;
	//
	return 0 ;
}