/* Include the unit testing library */
#define CATCH_CONFIG_MAIN //creates a main function as all CPP files need
#include <catch.hpp>

/* Include the code that we plan to test */
#include "code.hpp"

/* Create sub-categories to test with predicted outcomes */
TEST_CASE("Add Function")
{
	REQUIRE( add(1,2) == 3 );
	REQUIRE( add(1,1000) == 1001 );
	REQUIRE( add(0,0) == 0 );
}

TEST_CASE("formatName Function")
{
	REQUIRE( formatName("Salih") != "Hi! It's good to meet you Salih" );
	REQUIRE( formatName("Bob") != "Hi! It's good to meet you Bob" );
	REQUIRE( formatName("Hoofch") == "Hoofch" );
}
