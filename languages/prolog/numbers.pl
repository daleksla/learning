/*
    * This file contains example on how to use numbers in Prolog
    * Numbers are one of the three )decimal point are floats, else integers
    * Comparison *predicates*:
        * > : larger than
        * < : smaller than
        * >= : larger or equal to
        * =< : smaller or equal to
        * Can use either as infix or as standard predicate
*/

% positive(Float/Int)
positive(X) :-
    >(X, 0) . % OR use X > 0.

% negative(Float/Int)
negative(X) :-
    not(positive(X)).
