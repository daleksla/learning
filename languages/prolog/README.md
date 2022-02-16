# Prolog

Prolog is language following the logic programming paradigm - knowledge is derived by combining existing knowledge with logical rules applied between them. A prolog program consists of a sequence of facts and rules, which can then loaded by an interactive console, such that queries can be made on said information. It is an example of a declarative programming language (a black box approach, where a request is made and the 'how' (of processing) is left up to software).

This is known as 'rule based AI', as opposed to 'statistics-based AI' (which infers rules and links from data). Whilst the former is more accurate, adaptable and comprehensible for it's analysers / readers, it is also time consuming.

***

To get started:

1. Write a file (ending with the `.pl` extension) containing rules
> `<filename>.pl`
2. Run interactive console (e.g. `swipl`)
3. Load rules, in console, using `consult` command OR by placing rules filename in square brackets
>> `consult(<filename>)`
OR
>> `[<filename>]`
4. Have fun making queries, for example:
>> `rule(object)` % returns true / false
