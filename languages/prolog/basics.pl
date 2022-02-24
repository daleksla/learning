/*
    * This file contains the basic layout and syntax rules for all prolog programs
    * The generic name for all forms of Prolog data is "term" - four types
        * Atoms
            * Symbolic identifiers
                * names made up of letters, digits of underscores
                * they are essentially values
                * lowercase - they MUST be otherwise they no longer are symbolic identifiers
            * Strings
                * note: enclosed in single quotes
        * Numbers (see numbers.pl for usage)
        * Variables (see variables.pl for usage and purpose)
        * Complex terms - three types:
            * structures / facts: declaring things that are always true
                * known as predicate expressions (ie. <fact> is <args>)
                * essentially the most basic component in a prolog program
                * syntax: <structure_head>(arg1,...,argn)
                * Note: facts with differing ARITY (taking differing num of args) but with the same name need to be defined particularly:
                    * cluster rules which take x args together
                    * (then) the terms variant which takes y amount of objects
            * rules: declaring things that are true GIVEN a certain condition (see rules.pl)
            * questions / queries: finds out if a given goal is true (see queries.pl)
    * Note: inline comments start with '%', multi line comments are enclosed within c-style multi line comments
*/

% Starting Facts
indian(korma). % meaning of korma is a type of indian (food). Note: ends with fullstop. THIS IS A FACT
indian(tandoori).
indian(vindaloo).
mild(korma).
chinese(chow_mein).
chinese(chop_suey).
likes(bob, pizza). % a new rule. bob and pizza (together) fall in the category of (being) like(d)
likes(bob, cheeseburger).
likes(alice, salad).
likes(alice, sushi).
likes(salih). % variant of the likes rules taking different number of objects. here, salih falls into the category of 'like(ing)' everything (will always return true)

% ?- likes(alice, guacamole) % should return false
