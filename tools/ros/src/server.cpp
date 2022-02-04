#include "ros/ros.h"
#include "beginner_tutorials/AddTwoInts.h" //whenever we make messages / services, a custom header file is made

bool add(beginner_tutorials::AddTwoInts::Request& request, beginner_tutorials::AddTwoInts::Response& response)
{
	response.sum = request.a + request.b ; //calculate, store in response shared pointer (which caller has access to)
	return true ;
}

int main(int argc, char** argv)
{
	ros::init(argc, argv, "server") ; //create ROS node called 'server'
	ros::NodeHandle n ; //create communication access point to ROS
	
	ros::ServiceServer service = n.advertiseService("add_two_ints", add) ;
	ros::spin() ;	
}
