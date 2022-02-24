/*
    * This file demonstrates using queries
    * A query is a sequence (one or more) predicate expressions (sentences to be evaluated as true or false given the properties you also pass)
        * expressions chained using booleans ',' (AND), ';' (OR)

    * How prolog answers questions:
        * Examines knowledge it has (top to bottom) and finds all the facts or rule heads that match the given predicate
            * Process calls unification finds 'matching' facts / rules (see unification.pl)
            * It evaluates the proposition to true or false
        * if it finds a rule:
            * it then replaces the predicate with the rule body
            * It then breaks down the fetched components of the rule and evaluates each of its predicate components (recursively)
        * if the rule / fact found evaluated to false:
            * it tries searching for alternative rules / facts which match - process known as backtracking
        * if it can't reduce the query predicate further (exhaustive search inconclusive):
            * returns False

    * Note: can ask queries using predicate logic (see rules.pl)
    * Note: prolog saying a result is false means prolog cannot ascertain whether it is true (doesn't mean definitive false). works off a closed world model.
    * Note: you can negate the result of queries using not construct ( not(<fact/rule>) )
    **** Note: this file cannot be consulted and merely just shows examples of how to query something in different ways ****
*/

[basics]. % consult rules

indian(korma). % is korma a type of indian (different meaning when running in terminal despite exact same syntax)
                % note: this is a kind of predicate
