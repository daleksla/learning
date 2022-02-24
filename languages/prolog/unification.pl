/*
    * File shows how to perform unification

    * Unification is a process which finds 'matching' facts / rules
        * Unification is an algorithm for determining the substitutions needed to make two predicate calculus expressions match
        * When a query succeeds Prolog displays all variables that were bound by unification in forming the proof.
        * When Prolog backtracks in its proof of a query it undoes the corresponding bindings.
        * Uses syntactic pattern matching
            * For basic data
                * if knowledge and query alike make use of symbolic constants:
                    * they must match (the symbols) to be unified (trivial unification)
                * if one or more of them is a variable:
                    * unification CAN occur PROVIDING the value behind the variable(s) is bound and matches to the other or the variable is unbound
                    * When unbound, prolog just unifies anyway by binding the unbound variable to the data of what its comparing
            * For structures
                * Concerned matching identifers of structures to a given predicates, as well as matching arity values
                * Concerned with matching inner types (see above)

        * eg date(X, jan, 2021) unifies with date(25, jan, Y)
            * structure identifiers and arity matches, X CAN unify with 25, both jan symbolic constants match, 2021 can unify with Y

    * '=' (unification predicate): used to trigger unification
        * '\=' (negation of unification) : succeeds upon failure to unify
    * '==' (equality): compares whether two sides show the same expressions
        * Unlike '=', does not perform full unification such that unbound variables will not be assigned to to make unification occur
        * '\=' performs negation of the aforementioned
    * NEITHER OF THESE ARE TRUE COMPARISON. see variables.pl for the workaround for this which is one of the main purposes of variables
*/

isZero1(X) :-
    X=0. % will not perform comparison evaluation and therefore will only return true if X = 0 (rather than expression which will make 0) OR x is unbound

isZero2(X) :-
    X=0. % will only perform expression if X stores the same value (doesn't care about unbound)

% see variables.pl for how to truly see if a variable is 0
