import requests #import required module

"""We must be able to utilise the contents of the webpages we've extracted"""

def main():
	response = requests.get('https://api.github.com', verify=False)
	if response == False:
		print("Error")
	else:
		print("\033[2J\033[0;0H")
		results = response.json() #results is the dictionary to store our results
# 		for key, value in results:
# 			print(key,":", value)
	
if __name__ == '__main__':
	main()