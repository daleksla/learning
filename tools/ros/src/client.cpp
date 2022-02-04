#include "ros/ros.h"
#include "beginner_tutorials/AddTwoInts.h" //whenever we make messages / services, a custom header file is made

int main(int argc, char** argv)
{
	ros::init(argc, argv, "client") ; //create ROS node called 'server'
	ros::NodeHandle n ; //create communication access point to ROS
	
	ros::ServiceClient client = n.serviceClient<beginner_tutorials::AddTwoInts>("add_two_ints") ;
	beginner_tutorials::AddTwoInts srv ;
	srv.request.a = atoll(argv[1]);
  	srv.request.b = atoll(argv[2]);
  	
 	 if (client.call(srv)) ROS_INFO("Sum: %ld", (long int)srv.response.sum);
 	 else {
		ROS_ERROR("Failed to call service add_two_ints");
		return 1;
 	 }
}
