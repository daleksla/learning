#include "ros/ros.h"
#include "std_msgs/String.h"


void chatterCallback(const std_msgs::String::ConstPtr& msg) //Input in the form of a Boost Shared Pointer
{
	ROS_INFO("Message: [%s]", msg->data.c_str());
}


int main(int argc, char **argv)
{
	ros::init(argc, argv, "listener") ; //initialise node
	ros::NodeHandle n ; //grant access point for communication with ROS

	ros::Subscriber sub = n.subscribe("chatter", 1000, chatterCallback) ; //suscribe to a topic & provide a callback / function should a message be received
	ros::spin() ;
}

