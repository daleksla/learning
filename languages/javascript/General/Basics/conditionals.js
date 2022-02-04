/* The JavaScript language contains a number of conditional operators that work in the same way as in other languages
 * You can specify a block of code to run if a certain condition is true (ie. if statements)
 * Unlike Python, C etc., the conditional operator work slightly differently in JS
	 * The '==' operator will compare the values in the conditions, changing their datatypes if need be
		 * e.g. '12' == 12 (ie. string vs number) will result in true as they have the same value regardless of the datatype)
		 * This is a bad practise and should be avoided
	 * Instead, use the '===' operator - this is called the 'strict quality operator' - this will ensure both the value and type have to be the same 
  * Other operations we can use include the greater than operator ('>') and the less than operation ('<')
	  * We also have greater than or equal to ('>=')
	  * We also have less than or equal to ('<=')
 * Just like C++, the '||' operator means or, and the '&&' operator means and 
 * Instead of chained if statements, we can use also 'switch statements' - they are designed to managed multiple conditions 
	 * A switch statement takes a single parameter which is what each case will be tested against 
	 * Note: at the end of each case, end a 'break' keyword ; this will force the branch to exit once it's found the correct one 
	 * If it doesn't match any of the specific cases, we can use the 'default:' case to execute otherwise */

let hour = 12

if(hour === 12 || hour === 0) // this will execute so long as value & type matches
{
  console.log('It\'s noon!') //note: backslash makes the program ignore the next character (ie. it won't end the string)
}
else if (hour === 11 || hour === 1)
{
	console.log('It\'s nearly midday!')
}
else {
	console.log('It\'s a regular hour!')
}

let day = 0

switch(day) {
  case 0:
    console.log('Sunday')
		break
  case 1:
    console.log('Monday')
		break
	case 2:
		console.log('Tuesday')
		break
	case 3:
		console.log('Wednesday')
		break
	case 4:
		console.log('Thursday')
		break
	case 5:
		console.log('Friday')
		break
	case 6:
		console.log('Saturday')
		break
	default:
		console.log('Number out of range')
		break
}