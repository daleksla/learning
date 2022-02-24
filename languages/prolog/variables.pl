/*
    * This file shows how to create and manipulate variables in Prolog
    * Assigning variables is done using 'is' Command
        * e.g. <Var>/<number> is <expres>
            * where Var is a unbound (unassigned) variable / number is a single number and expres is bound (created (if a variable) / immediately computable) variable OR an expression
    * 'is' always forces the computation on the right to occur (as in doesn't treat right expression like predicate expression)
    * Note that 'is' IS A PREDICATE. if the assignment was possible, 'is' returns true, else false
    * Variable in Prolog are IMMUTABLE (ie. cannot change upon initial assignment/creation) - in other words, 'is' returns false upon being assigned a different value (and true if its asked to assign the same)
    * Must be defined as upper case

    * Main use cases:
        * Therefore one of the main usages of the 'is' command is evaluation - we can see if one value matches another by whether an expression (which is force computed)
        * The other usage is passing in an undefined variable which would then be assigned to via 'is' (which can therefore work as the return value of a function)

    * var predicate can check IF variable is bound or not:
        * Syntax: var(<Variable>)

    * Note: if a given argument is useless in a scenario BUT maintaining arity is needed, use _ (anonymous variable) in place of variable
        * prevents prolog warning(s) of singletons
    * Note: the variable dies in the scope it was created in. In an interpretter for example, you are not able to declare a variable on one line and use it on the next. In that exanple, you'd have to define X at the start, then chain (using boolean AND) the other variable which uses the first variable, as so on
*/

% using variables

isZeroBest(X) :-
    0 is X % providing X is assigned to, will return True.

% using variables to return values

squared(X, Y) :-
    Y is X * X. % here, X * X is forced to run  and attempts to assign it to Y
    % if Y is set to a different value, assignment cannot work so false.
    % if it isnt though, assignment is possible regardless and is set to the value of X^2 - this allows us to perform computation

% we could query this in two ways:
% 1. X is 2, Y is 4, squared(X, Y).
%    * This returns true
% 2. X is 2, squared(X, Y).
%    * Y = 4 is whats returned
