/* Include the unit testing library */
#define CATCH_CONFIG_MAIN
#include <catch.hpp>

/* Include the code that we plan to test */
#include "code.hpp" //only header file needed (just compile with implementation at run time)

/* Create sub-categories to test with predicted outcomes */
TEST_CASE("getName test")
{
	Human human("Salih", 20, {8, 12, 2000}, "Birmingham", "United Kingdom") ; //create object
	REQUIRE( human.getName() == "Salih" ); 
	REQUIRE( human.getName() != "Talih" );
}

TEST_CASE("formatDob test")
{
	Human human("Salih", 20, {8, 12, 2000}, "Birmingham", "United Kingdom") ;
	REQUIRE( human.formatDob() == "8/12/2000" );
	REQUIRE( human.formatDob() != "Talih" );
	REQUIRE( human.formatDob() != "08122000" );
}