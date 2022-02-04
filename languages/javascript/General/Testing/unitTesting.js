/* Unit testing is a process whereby we write automated tests to check that the code runs as it should
 * We can ensure through testing that
	 * it responds correctly without crashing if the data is invalid
	 * it does what you expect when you supply it with valid data
	 * Finally, it should ensure previous functionality is not comprimised
 * Note: unit tests are designed to test the functions in your project and not the interface
	 * Therefore you need to separate these
 * To write test-code, format the file name in the following way: test-insertFileName.js
	 * Doing so will store the tests for that file in the test suite
	 * Each module should have only one test suite, with multiple test functions within
 * The basic header of each test case in the test file:
	 * test('test case #1', test=> {function goes here}) 
 * Tests must bestructured in a logical manner & each test for one thing
 * They should include three steps
	* Arrange – The first step is to make sure the system is ready
		* e.g. to clear out any old data and reset the system.
	* Act – perform an action
		* This might typically be to call a function with a specified set of parameters. Some tests might use valid ones but in some tests you would pass in invalid parameters to make sure the function responds correctly without crashing the program.
	* Assert – run some checks on the result of the function call
		* This might be to check the return value or to make sure that the function threw the correct error
		* Each assertion returns true if the condition is met but, if the condition is not met, the assertion returns false and the test immediately fails
		* Ava comes with a comprehensive set of built-in assertions
			* All of these accept an additional parameter representing the message to display if the test fails (ie. if you put a message in the brackets of the assertion, it'll display when it fails)
		* Common assertions include test.pass(), test.fail(), test.is(value, expected), test.truthy('value') //ie. if the value isn't 0, null, NaN etc.
		* Assertion Plans are designed to check that the required number of assertions have run 
			* To use this feature, at the top of your code write 'test.plan(n)', where n is the number of assertion you want run
 * Note: there are a number of features of good unit tests
	* Fast – the test should run really quickly because you will end up with lots of them and you should run them frequently
		* If the tests are slow you won’t want to run them
	* Isolated – When you run the test suite the tests are run asynchronously and in parallel and there is no guarantee they will always run in the same order
		* In the arrange part of each test you should ensure there is no data added by another test
	* Repeatable – You should get the same results whether you run the test once or ten times
	* Self-Validating – all tests should be pass/fail
		* If you have to check a set of data manually to see the pass status you slow the process down and it also means you can’t run them as part of an automated continuous integration pipeline (don’t worry if you don’t know what this is yet).
	* Timely – the tests should be written just before they are implemented
		* Write a single test and get it to pass before writing the next. The process should be quick
 * Note: we can write a host of test code but test only certain one's by appending '.only' after the test keyword
	* e.g. test.only('test case #1', test=> {function goes here}) 
 * To finally run the test, type 'npm test' on the command line */

import test from 'ava'
import {clear, add} from './myCode.mjs'

//the code below will be imported and tested
// function clear() {
// 	data = []
// }

// function add(item, qty = 1) {
// 	qty = Number(qty)
// 	if(isNaN(qty)) throw new Error('qty must be a number')
// 	data.push({item: item, qty: qty})
//   return true
// }

test('add a single item', test => { //here we create the test case ; we pass it the name of the case and the function that'll test it
  // arrange - prepare system for test
  test.plan(1)
  clear()
  // act - perform an action
  add('bread')
  // assert - test if action was expected
  test.is(count(), 1, 'the qty is not correct')
})

test('add a single item – BAD!', test => {
	//no assertion on how many assertions will be used
  clear()
  const ok = add('bread')
  test.truthy(ok) //we haven't tested here if the add function even works, bad code!
})
