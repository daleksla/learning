/*
    * This file shows how to use conditional statements in Prolog
    * There is nothing called conditionals per se considering how everything is a predicate in Prolog but we can simply define two rules / predicates which will evaluate to true given a certain condition
        * However, Prolog's backtracking algorithm, which evaluates all possible predicates which can evaluate to true, is inhibitive of performance in this circumstance - we don't want further unification to attempt to find things that are true (see unification.pl) because the logic of an if statement is that only one of the cases we write are going to be true
        * We can avoid this using something known as 'cuts' - a predicate represented by an exclamation mark ('!') which informs the backtracking search algorithm that, so long as this is reached within a predicate, it needn't look for another predicate
            * We therefore can the cut using a boolean AND to a statement which has evaluated as true
            * We can classify cuts into two types:
                * Green Cuts: Cuts which are introduced to remove what the programmer knows are useless computations. I.e. running the code with and without this cut gives the same answer but just different computation time.
                * Red Cuts: Cuts introduced to make the program run differently by eliminating some possible solutions. These change the logical meaning of code
            * you should use green cuts but you are advised against using red cuts
            * Syntax:
                * Basic: <predicate_name> :- <predicate_cond_1>, !.
                         ...
                         <predicate_name> :- <predicate_cond_n>.
                * Nicer: <predicate_name> :- p -> q; r
                    * a shorthand way of doing a simple if else statement
*/

% basic if statement
minimum(X,Y,X) :- X<Y, !. % this will evaluate to true IF X is smaller than Y and will return X (if third parameter is undefined (see variables.pl). cut tells it that, providing this predicate is true
minimum(X,Y,Y) :- X>=Y. % if X is larger of equal to Y, return Y. no cut as it logically makes no sense as there is no ifs after this

% more complex if statement
assignClass(Mark, first)       :- Mark>=70, ! .
assignClass(Mark, upperSecond) :- Mark>=60, ! .
assignClass(Mark, lowerSecond) :- Mark>=50, ! .
assignClass(Mark, third)       :- Mark>=40, ! .
assignClass(Mark, fail)        :- Mark<40.

% purely if else statement can be rewritten as this
s :- p -> q ; r.
