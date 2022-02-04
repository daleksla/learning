// Use child_process.spawn method from 
// child_process module and assign it 
// to variable spawn 
const spawn = require("child_process").spawn; 

// Parameters passed in spawn - 
// 1. type_of_script 
// 2. list containing Path of the script 
// and (system) arguments for the script 

var process = spawn('python',["./hello.py", 'Salih', 'Ahmed'] ); 

// Takes stdout data from script which executed 
// with arguments
process.stdout.on('data', data => { 
	console.log(data.toString()) //here we print the values in the stdout channel
}) 
