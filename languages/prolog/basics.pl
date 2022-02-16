/*
    * This file contains the basic layout for all prolog programs
    * Each prolog program contains a series of rules (be they singular or combinations of multiple rules), each ending with a fullstop (ie. '.')
        * The most basic rule has the syntax <property>(<object>). (ie. the object is a type of property)
        * A rule can establish multiple objects to a certain property: <property>(<object1>, ..., <objectn>).
        * Note: a rule taking differing amounts of objects need to be defined particularly:
            * x amount of objects must be defined together / next to each other
            * (then) the rules variant which takes y amount of objects
            * ... etc.
    * Note: inline comments start with '%', multi line comments are enclosed within c-style multi line comments
*/

% Starting Facts
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
