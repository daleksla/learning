import requests #import required module
from getpass import getpass #allows us to securely enter password

"""Authentication helps a service understand who you are. 
Typically, you provide your credentials to a server by passing data through the Authorization header (or a custom header defined by the service). 
Most request functions provide a parameter called auth, which allows you to pass your credentials."""

def main():
	# We will search GitHub's repositories for requests
    requests.get('https://api.github.com/user', auth=('username', getpass()))
	#We passed the parameters of our search along with the URL
	results = response.json() #we store the results in a dictionary
	
if __name__ == '__main__':
	main()