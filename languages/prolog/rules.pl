/*
    * This file contains how to derive new terms using conditional statements
    * A rule is a type of term (see basics.pl) which is used to derive new facts
        * (typically) Creates predicate logic - rules about unknown object which, when specified, become propositions and are hence true/false evaluated
            * Since a predicate can be true or false depending on the input, quantifiers allow us to 'formalise properties' of the predicates (ie assert what kind of value should be returned)
                * Existential quantifier (backwards E): meaning of there is at least one specifications of the unknowns / given inputs where predicate is true
                * Universal quantifier (upside down A): meaning of all specifications of the unknowns / given inputs result in predicate being true
        * Syntax:
            * <predicateH>(<Variable_name>) :- <predicate_1> <boolean combiner> ... <boolean combiner> <predicate_n>.
                * Variables in Prolog are used to specify genericity
                    * Use is universally quantified (ie. a given rule states that X always (where X is a variable) has to suffice conditions) - one of the millions of values X can hold isnt good enough.
                    * (see variables.pl for full use case)
        * We can generate new rules using one or more existing rules
        * The if keyword is represented by a colon and a hyphen (':-')
        * Boolean combiner 'and' is represented using commas (',') and 'or' is represented using semicolons (';')
        * The result of other facts and rules can be negated using the not construct ( not(<fact/structure>) )
        * Note: it is important to ensure rules may not become infinite derivations (e.g. a rule which summons another rule which then summons it)
*/

% dummy facts (from basics.pl) - ignore
indian(korma). % meaning of korma is a type of indian (food). Note: ends with fullstop
indian(tandoori).
indian(vindaloo).
mild(korma).
chinese(chow_mein).
chinese(chop_suey).
likes(bob, pizza). % a new rule. bob and pizza (together) fall in the category of (being) like(d)
likes(bob, cheeseburger).
likes(alice, salad).
likes(alice, sushi).
likes(salih) % variant of the likes rules taking different number of objects. here, salih falls into the category of 'like(ing)' everything (will always return true)

% rules relevant to this file
likes(bob,Food) :- % bob likes variable Food if... RULE HEAD
    not(chinese(Food). % ... the Food variable is NOT a type of chinese.

likes(alice, Food) :- % alice likes variable Food if...
    indian(Food), mild(Food). % ... Food is a type of indian AND food is a type of mild

% following is example  of an infinite loop
man(adam). % define initial fact
woman(eve).

man(X) :-
    not(woman(X)).

woman(X) :-
    not(man(X)).

% here, man is not woman, where woman is not man, etc. recursive hell
