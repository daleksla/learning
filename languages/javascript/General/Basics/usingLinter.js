/* Linting is a concept where code is tested against a set of rules, regardless whether the code is legal or not
	 * This is done to ensure you are not using what are considered bad language features.
	 * This will also ensure optional syntax (such as indentation and semicolons) is done in a consistent manner
	 * Finally, it ensures the code written is easy to maintain
 * To do so, we need to use a third-party module called 'eslint'
	 * 'eslint' is a binary file - binary files are installed in the current directory of the terminal, in the subfolder node_modules in the subfolder .bin
		 * ie. It's locatable in ./node_modules/.bin/
 * To use 'eslint', run the following command:
	 * ./node_modules/.bin/eslint file-name.js
	 * If it finds any problems, they're outputted to the console, along with the position in the file (line, column), a description and the rule broken
		 * Serious issues are classed as 'errors'
		 * Less critical issues are classed as 'warnings'
 * Instead of running separate checks on every file, we can specify the directory we want to check and it will automatically scan all the subdirectories
	 * e.g. To scan all the files in the current directory, use './node_modules/.bin/eslint .' on the command line
 * To create your own rules (ie. if you do not want to use the default ones), create / modify the '.eslint.json' file
 * To make exceptions for file checking, create / modify the '.eslintignore' folder and include the files / path to files to ignore
 * Note: to save time, create an alias to the binary file in the terminal
	 * ie. alias eslint="./node_modules/.bin/eslint"
	 * This way, you can just type 'eslint file-name' on the command line