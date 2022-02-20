/*
    * This file demonstrates using queries
    * Two different types of queries:
        * Proposition: true or false statements
        * Predicates: A statement where there is an unknown factor
            * Since a predicate can be true or false depending on the input, quantifiers allow us to 'formalise properties' of the predicates (ie assert what kind of value should be returned)
                * Existential quantifier (backwards E): meaning of there is at least one specifications of the unknowns / given inputs where predicate is true
                * Universal quantifier (upside down A): meaning of all specifications of the unknowns / given inputs result in predicate being true
    * Note: this file cannot be consulted and merely just shows examples of how to query something in different ways
*/

[basics]. % consult rules

indian(korma). % is korma a type of indian (different meaning when running in terminal despite exact same syntax)
               % note: this is a kind of proposition

Month = korma
indian(Month)
