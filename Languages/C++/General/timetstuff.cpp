#include <iostream>
#include <ctime>
#include <string>
#include <vector>
#include <iterator>
#include <ctype.h>
#include <algorithm>
#include <typeinfo>
#include <map>
using namespace std ;

int main()
{
	time_t tt; 

	// Declaring variable to store return value of 
	// localtime() 
	struct tm * ti; 

	// Applying time() 
	time (&tt); 

	// Using localtime() 
	ti = localtime(&tt); 

	string bob = string(asctime(ti));
	
	cout << bob << endl ;
	
	map<string, int> months = {
		{"Jan", 1}, {"Feb", 2}, {"Mar", 3}, {"Apr", 4}, {"May", 5}, {"Jun", 6}, {"Jul", 7},
						{"Aug", 8}, {"Sep", 9}, {"Oct", 10}, {"Nov", 11}, {"Dec", 12}
	} ;
	
	int counter = 0 ;
	
	string x = "" ; 
	
	vector<int> currentDate ;
	
	for(auto it = begin(bob) ; it != end(bob) ; it = next(it))
	{
		char tis = *it ;
		if(tis == ' ')
		{
			counter += 1 ;
			continue ;
		}
		
		if(counter == 1) //month
		{
			auto itz = next(it) ;
			char thingy = *itz ;
			if(thingy == ' ')
			{
				x.push_back(tis) ;
				currentDate.push_back(months[x]) ;
				x = "" ;
			}
			else 
			{
				x.push_back(tis) ;
			}
			continue ;
		}
		else if(counter == 2) //month
		{
			auto itz = next(it) ;
			char thingy = *itz ;
			if(thingy == ' ')
			{
				x.push_back(tis) ;
				currentDate.push_back((stoi(x))) ;
				x = "" ;
			}
			else 
			{
				x.push_back(tis) ;
			}
			continue ;
		}
		else if(counter == 4) //month
		{
			auto itz = next(it) ;
			char thingy = *itz ;
			if(!isdigit(thingy))
			{
				x.push_back(tis) ;
				currentDate.push_back((stoi(x))) ;
				x = "" ;
				break ;
			}
			else 
			{
				x.push_back(tis) ;
			}
			continue ;
		}
		
	}
	
	
	for(auto it = begin(currentDate) ; it != end(currentDate) ; it = next(it))
	{
		cout << *it << endl ;
	}

// 	cout << typeid(*asctime(ti)).name()<<endl;
	//
	return 0 ;
}