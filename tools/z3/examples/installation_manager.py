""""
    * @brief Solve an installation manager (dependencies and conflicts) problem as an example of real z3 and constraint programming usage

    * Consider the problem of installing a new piece of software on a system. Many packages depend on other packages to provide some functionality. Each distribution contains a metadata file that outlines those requirements for each package. The metadata includes names and version numbers for dependencies and conflicts
"""

import z3

"""
    * @brief create_basic_dependency_constraints - creates implies constraint between a package and every single dependencies (ie AND)
    * this is because installing the package implies that the other package is already installed - if it dep isnt installed, this implies will evaluate to false. the And means that non of the implications can be false lest the entire And and dependencies section becomes false
    * @param z3.Bool - package to create dependencies for
    * @param [z3.Bool] - list of depedency packages
"""
def create_basic_dependency_constraints(package, dependencies):
    return z3.And([z3.Implies(package, dependency) for dependency in dependencies])


"""
    * @brief create_xor_dependency_constraints - creates implies constraint between a package and any of the given dependencies
    * this is because installing the package implies that the other package is already installed - if it dep isnt installed, this implies will evaluate to false. the Or means that we only need one of these dependency packages present
    * @param z3.Bool - package to create dependencies for
    * @param [z3.Bool] - list of depedency packages
"""
def create_xor_dependency_constraints(package, dependencies):
    dependencies = z3.Or([z3.Implies(package, dependency) for dependency in dependencies])
    return dependencies


"""
    * @brief create_conflict_constraints - creates Or(NOT) constraint
    * this is because we need to make sure all of the conflicting packages are not present. therefore when running the solver, if any one of these packages are found (ie true) the statement will evaluate to false
    * @param z3.Bool - package to create conflict constraints for
    * @param [z3.Bool] - list of packages to make conflicts upon
"""
def create_conflict_constraints(package, conflicts):
    return z3.Or([z3.Not(conflict) for conflict in conflicts])


def installation_manager():
    a, b, c, d, e, f, g = z3.Bools("a b c d e f g")

    dependencies1 = create_basic_dependency_constraints(a, [b])
    dependencies2 = create_basic_dependency_constraints(b, [c, d])
    dependencies3 = create_xor_dependency_constraints(c, [d, e])
    dependencies4 = create_xor_dependency_constraints(c, [e, g])
    conflicts1 = create_conflict_constraints(d, [e])
    conflicts2 = create_conflict_constraints(a, [f])

    z3.solve(dependencies1, \
    dependencies2, \
    dependencies3, \
    dependencies4, \
    conflicts1,
    conflicts2,
    a \
    ) # based on the given dependencies and conflicts, and the fact we want package a, find a solution of whhich packages we can have and which of those we cant

if __name__ == "__main__":
    installation_manager()
