# z3

z3 is a SAT / SMT solver, where SAT problems are a category of logical formulas consisting of Boolean formulas to which a deduction is to be made as to if the formula can be satisfied or not) & SMT is a more generalised version of SAT such that it can involve more complex types such as real numbers, lists, etc.. z3 consists of both a SAT solver (which deconstructs a given problem into a Boolean skeleton) and a theory solver to see if that solution makes sense (ie. if the polynomial constraints can take those truth values).

Z3 is used in many applications such as: software/hardware verification and testing, constraint solving, analysis of hybrid systems, security, biology (in silico analysis), and geometrical problems. It has since been released as an open-source tool.

This folder will demonstrate how to use z3's Python API (though there are API's available for C/C++, C#, and others).

See [another tutorial](https://ericpony.github.io/z3py-tutorial/guide-examples.htm) for using the z3 API in python
