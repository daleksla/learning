/*
    * This file is concerned with manipulating lists in Prolog
    * Creating:
        * x number of comma seperated elements enclosed in sqaure brackets, where x is non negative
        * Not type specific
    * Appending:
        * Syntax: append(<list>, <list_to_append>, <var_to_store_combined_list>)
        * Note: inefficient due to inbuilt linkedlist structure
    * Prepending:
        * Every non empty list can be split into a head and a tail, where the head is the first element and the tail is a list of the remaining elements
            * Syntax: [<elementToAddToFirst> | <list>]
    * Length: len(<list>, <var_of_list>)
    * Note: pattern matching for lists is available
        * Syntax for empty list matching: <predicate_name>([])
        * Syntax for head, tail splitting: <predicate_name>([<head_var_name>|<tail_var_name>])
    * Note: unifying (assigning) lists requires '=' expression (as opposed to is)
*/

list = [ford | [vauxhall, skoda]]

% creating range lists by going from S->E inclusively and prepending to list
range(S, S, [S]).
range(S, E, L) :-
    NewS is S+1,
    range(NewS, E, NewL),
%    append([S], NewL, L). % inefficient as hell
    L = [S | NewL]. % more efficient prepending

% recursively goes from S->E at increments of J. if E−S were a multiple of J, it adds J
range(S, E, _, L) :-
    S == E, % if S doesnt exceed J (therefre S,E difference is perfectly divided)
    L = [S], % allow S (which has number J) to be added
    !. % cut

range(S, E, _, L) :-
    S >= E, % if S is larger or equal to than E (not perfectly divisible but we've exceeded, meaning we know for a fact they dont perfectly divide and we've gone past the range specified)
    L = [], % return empty list
    !. % cut

range(S, E, J, L) :-
    % else
    NewS is S+J,
    range(NewS, E, J, NewL),
    append([S], NewL, L).

% sums values in a given list
sum([],0). % pattern matching
sum([H | T], Sum) :-
  sum(T, NewSum),
	Sum is H + NewSum.
