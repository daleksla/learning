import requests #import required module

"""One common way to customize a GET request is to pass values through query string parameters in the URL. 
To do this using get(), you pass data to params. 
In this file, we will use GitHub’s Search API to look for the requests library """

def main():
	# We will search GitHub's repositories for requests
	response = requests.get('https://api.github.com/search/repositories', params={'q': 'requests+language:python'},)
	#We passed the parameters of our search along with the URL
	results = response.json() #we store the results in a dictionary
	
if __name__ == '__main__':
	main()