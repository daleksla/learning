/*
    * This file demonstrates recursive functionality in Prolog
    * Note: to see how to give outputs etc. refer to variables.pl
    * Structure:
        * define base cases as facts (with the components being symbolic constants)
        * define general case as rules
        * both must have the same arity and identifier
            * each should have an additional argument which should be queried using variable in its place to store the output of a given rule / fact
*/

% factorial equation: n! = 1 ∗ 2 ∗ ⋯ ∗ (n − 1) ∗ n

% base case - 0 input, 1 output
factorial(0, 1).

% general case (rule) - N input, NF output
factorial(N,NF) :- % takes N, NF is for output
    N>0, % n is larger than 0 == TRUE
    NM1 is N-1, % initialise value of variable which is N - 1
    factorial(NM1, NM1F), % recursive apply rule
    NF is N*NM1F % store output in NF

% equation: b^e = b ∗ b^e−1

% base case - anything to the power of 0 is 1. B isn't used so put anonymous variable
power(_, 0, 1).

% recursive case
power(B, E, Ans) :-
        NewE is E - 1, % calculate E - 1
        power(B, NewE, NewAns), % calculate the power of B to E - 1 and save answer
        Ans is B * NewAns. % set Ans to B * b^(e-1) (aka NewAns)
