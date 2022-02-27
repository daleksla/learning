/*
    * This file contains examples for how to do IO in Prolog
    * Several predicates to perform IO:
        * Output:
            * write - writes a single term to a terminal, adds new line by default
                * Syntax: write(<term>)
            * tab - takes an integer and prints that number of spaces
                * tab(<num_spaces_desired>)
            * nl - prints a newline character
                * syntax: nl
        * Input:
            * read - reads a term and sets a variable to what is read. stops reading upon seeing a fullstop and whitespace character
                * Note: rather than creating a string, it actually just puts the code straight into the variable AS code. allows for injection etc.. UNSAFE!!!
                * Syntax: read(<unassigned var>)
            * read_string - the safe, more involved signature of the above
                * syntax: read_string(<stream>, <ending_char>, <padding_char>, <end_char_storing_var>, <variable_for_input_storage>)
                    * where stream is place to be read from (user_input flag for stdin), ending_char is the character which indicates end of input (such as '\n'), padding_char is padding character that should be ignored, end_char_storing_var is a variable to hold the end character read, variable_for_input_storage is to store string read in its entirity).
            * note: to convert input from string to number, use 'number_string' predicate
                * syntax: number_string(<variable_to_store_num>, <variable_storing_string>)
*/

% basic stuff - ignore
assignClass(Mark, first)       :- Mark>=70.
assignClass(Mark, upperSecond) :- Mark<70, Mark>=60.
assignClass(Mark, lowerSecond) :- Mark<60, Mark>=50.
assignClass(Mark, third)       :- Mark<50, Mark>=40.
assignClass(Mark, fail)        :- Mark<40.

% IO predicate (man I hate prolog)
assignToUser :-
    write("Please enter your mark: "),
%    read(X), % BAD read
    read_string(user_input, '.', ' ', _, StringNumber),
    number_string(IntOfString, StringNumber),
    assignClass(X, Grade),
    write(Grade).
