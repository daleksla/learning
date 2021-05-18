#include "ros/ros.h"
#include "std_msgs/String.h" //to communicate in the format of ROS string messages
#include <sstream> //to be able to treat strings like streams

int main(int argc, char** argv)
{
	ros::init(argc, argv, "talker") ; //create node 'talker'
	
	ros::NodeHandle n ; //object allowing us to communicate with ROS system
	
	ros::Publisher chatter_pub = n.advertise<std_msgs::String>("chatter", 1000) ; //create a topic calling 'chatter' that uses Strings to commmunicate
	
	ros::Rate loop_rate(10) ; //set how fast we want to run
	//allows you to specify a frequency that you would like to loop at
	//It will keep track of how long it has been since the last call to Rate::sleep(), and sleep for the correct amount of time
	
	for(int i = 0 ; ros::ok() ; i++)
	{
		std_msgs::String message ; //object we'll send to topic
		std::stringstream ss ; ss << "hello world" << i ; message.data = ss.str() ; //create stringstream, add content, make it into a string and make it messages data property
		chatter_pub.publish(message) ; //send message 
		ros::spinOnce() ; //trigger callback of receiving node listening to topic
		loop_rate.sleep() ; //let the loop sleep to make sure we maintain our rate (ie sleep so only one message is sent in an appropriate amount of time
	}
}
