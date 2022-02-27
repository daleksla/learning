/*
    * This file contains exampels to use, manipulate the Prolog predicates and the knowledgebase generally at a high level
    * There are other ways of defining facts and rules statically in Prolog files:
        * Viewing knowledge:
            * listing(<predicate_name>)
        * Adding knowledge:
            * Appending to knowedgebase:
                * assert(<predicate>)
                * assertz(<predicate)
            * Prepending knowledgebase:
                * asserta(<predicate>)
            * Note: Predicates that change during runs are known as dynamic. You are expected to flag up such predicates when writing your knowledge base
                * Syntax: :- dynamic <predicate_name>/<arity>
                * Note: brand new predicates inserted are automatically given this notation
        * Removing knowledge:
            * Removing particular knowledge:
                * retract(<predicate_name>(...))
            * Removing first instance of knowledge:
                * retract(<predicate_name>(_))
            * Removing all instances of knowledge with given name:
                * retractall(<predicate_name>(_))
            * Note: derivations from retracted facts will persist regardless of whether or not the facts they're based on do not exist
    * We can make Prolog answer a specific query before any other automatically by placing a command in the knowledgbase
        * Syntax: :- initialization <query_name>
    * Ending prolog:
        * Ending running of a given running query: break
        * Ending program entirely: halt
*/

:- dynamic happy/1.
happy(alice).
assert((naive(X):-  happy(X))).
assert(happy(bob)).
