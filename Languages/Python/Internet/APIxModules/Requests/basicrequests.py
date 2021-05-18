import requests #import required module

"""The requests library is the de facto standard for making HTTP requests in Python. 
It abstracts the complexities of making requests behind a beautiful, simple API """

def main():
	#HTTP methods such as GET and POST, determine which action you’re trying to perform when making an HTTP request. 
	#One of the most common HTTP methods is GET. The GET method indicates that you’re trying to get or retrieve data from a specified resource. 
	#To make a GET request, invoke requests.get(<URL>)
	response = requests.get('https://api.github.com')
	#You’ve captured the return value of get(), which is an instance of Response, and stored it in a variable called response. 
	#You can now use response to see a lot of information about the results of your GET request.
	#The first bit of information that you can gather from Response is the status code. 
	#A status code informs you of the status of the request (ie. whether it was successful or not)
	#Status code's are accesible with method .status_code (in this case, response.status_code)
	#A status code of 200 is sucessful, whilst a code of 404 is not. 
	#However, you can use our variable as a boolean (if(response == True) etc.)
	
	#We should prevent our program from wasting too much time on a request
	#We can set how much time it can take using a 'timeout' parameter (in seconds)
	response = requests.get('https://api.github.com', timeout=3.05)
	
	#Sometimes we cannot access what we want due to 'SSL certificate verification' (set on by default)
	#To disable it, simply pass another parameter called 'verify' and set it to false
	response = requests.get('https://api.github.com', timeout=3.05, verify=False)
	
	#There are two ways of accessing said contents if the extraction was sucessful ;
	#We could extract the raw bytes (response.content) OR we could convert them into a string (response.text)
	#However we could go further and create a dictionary (only in some cases), by using response.json()
	results = response.json() #results is the dictionary to store our results
	
	#We can also examines the headers of the data sent back
	#(they provide data on the request such as the content type of the response payload& time limit on how long to cache the response)
	#This process also returns a dictionary
	headers = response.headers
	
if __name__ == '__main__':
	main()