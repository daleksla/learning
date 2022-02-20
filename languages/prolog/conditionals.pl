/*
    * This file contains how to derive new terms using conditional statements
    * We can generate new rules using one or more existing rules
    * The if keyword is represented by a colon and a hyphen (':-')
    * Boolean combiner 'and' is represented using commas (',') and 'or' is represented using semicolons (';')
    * Full if syntax:
        * Single existing rule:
            <property>(<object>/<variable>) :-
                <existing_property>(<object>/<variable>).
        * More than one existing rules:
            <property>(<object>/<variable>) :-
                <existing_property_1>(<object>/<variable>).
                <boolean combiner>
                ...
                <boolean combiner>
                <existing_property_n>(<object>/<variable>).
        * Note: a variable is a placeholder (e.g. bob likes x if x is chinese where x is then substituted)
            * By convention it is capitalised and EVERYTHING ELSE IS LOWER CASE
*/

% dummy rules (from basics.pl)
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
likes(bob,Food) :- % bob likes variable Food if...
    chinese(Food). % ... the Food variable is a type of chinese

likes(alice, Food) :- % alice likes variable Food if...
    indian(Food), mild(Food). % ... Food is a type of indian AND food is a type of mild
