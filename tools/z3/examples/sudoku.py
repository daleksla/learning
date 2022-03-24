import z3

""""
    * @brief Creating and managing a sudoku grid as an example of real z3 and constraint programming usage
"""

"""
    * @brief constrain_grid - returns tuple of constraints for grid
    * @param [[z3.Int]] - plain unconstrained grid
    * @return ([z3.And], z3.Distinct)
        * #1 - 81 constraints in that each elemenet should be > 0, < 10
        * #2 - a list of 9 Distinct constraints (one for each sublist) for unique row vals
        * #3 - a list of 9 Distinct constraints (one for each sublist) for unique col vals
"""
def constrain_grid(plain_grid):
    conditioned_elems = [z3.And(plain_grid[outer][inner] > 0, plain_grid[outer][inner] < 10) for outer in range(0, 9, 1) for inner in range(0, 9, 1)]

    conditioned_rows = [z3.Distinct(plain_grid[i]) for i in range(0, 9, 1)] # Distinct is a handy z3 function applicable to a list of variables such that it encodes the condition that must be all different to each other. here, for each list / row, we make the z3.Ints distinct

    conditioned_cols = [z3.Distinct([plain_grid[row][elem] for row in range(0, 9, 1)]) for elem in range(0, 9, 1)] # get the nth element of each row, turn it into a list and make each of them distinct. repeat for each col

    conditioned_sub_boxes = [z3.Distinct([plain_grid[row][col] for row in range(i, i+3, 1) for col in range(i, i+3, 1)]) for i in [0, 3, 6]] # group into sets of 3 col and row wise, make each distinct, repeat for next sets of three

    return conditioned_elems, conditioned_rows, conditioned_cols, conditioned_sub_boxes


"""
    * @brief init_blank_grid - forms blank 9x9 classic sudoku grid restricted only to digits (1-9)
    * @return [[z3.And]] - list containing list of elements (z3.Int's), where each sublist represents each ROW
    * each elem structured as <x>_<y>, where x is row, y is col

"""
def init_blank_grid():
    return [[z3.Int("{0}_{1}".format(outer, inner)) for inner in range(1,10,1)] for outer in range(1,10,1)] # create list of lists


"""
    * @brief init_set_grid - forms 9x9 classic sudoku grid restricted only to digits (1-9) with some preset values
    * @param [[int]] - 2d list, each sublist containing 9 integers, where 0 means blank and anything else is a preset request
    * @return [[z3.And]] - list containing list of elements (z3.Int's), where each sublist represents each ROW
    * each elem structured as <x>_<y>, where x is row, y is col

"""
def init_set_grid(filled_list):
    blank_list = [[z3.Int("{0}_{1}".format(outer, inner)) for inner in range(1,10,1)] for outer in range(1,10,1)] # create list of lists

    value_constraints = [blank_list[outer][inner] == filled_list[outer][inner] for outer in range(0, 9, +1) for inner in range(0, 9, +1) if filled_list[outer][inner] != 0]

    return blank_list, value_constraints


def plain_sudoku():
    # create variables and relevant constraints
    plain_grid = init_blank_grid()
    elem_constraints, row_constraints, col_constraints, sub_box_constraints = constrain_grid(plain_grid)

    print("elem constraints:", elem_constraints)
    print()
    print("row_constraints:", row_constraints)
    print()
    print("col_constraints:", col_constraints)
    print()
    print("sub_box_constraints:", sub_box_constraints)
    print()
    print("########################################")

    # create solver
    s = z3.Solver()
    s.add(elem_constraints)
    s.add(row_constraints)
    s.add(col_constraints)
    s.add(sub_box_constraints)

    if(s.check() == z3.sat):
        model = s.model()
        solution = [[model.evaluate(plain_grid[row][col]) for row in range(0, 9, 1)] for col in range(0, 9, 1)] # for each z3,Int in model  index it for the value. get one elem at a time to get each row and put it in a list and repeat for each row
        print("Solution: ")
        for i in range(0, 9, 1):
            if i == 3 or i == 6 or i == 9:
                print("---------------------------------")
            print(solution[i])

def preset_sudoku():
    # create variables and relevant constraints
    instance = [[0,0,0,0,9,4,0,3,0],
            [0,0,0,5,1,0,0,0,7],
            [0,8,9,0,0,0,0,4,0],
            [0,0,0,0,0,0,2,0,8],
            [0,6,0,2,0,1,0,5,0],
            [1,0,2,0,0,0,0,0,0],
            [0,7,0,0,0,0,5,2,0],
            [9,0,0,0,6,5,0,0,0],
            [0,4,0,9,7,0,0,0,0]]

    plain_grid, val_constraints = init_set_grid(instance)
    elem_constraints, row_constraints, col_constraints, sub_box_constraints = constrain_grid(plain_grid)

    print("elem constraints:", elem_constraints)
    print()
    print("row_constraints:", row_constraints)
    print()
    print("col_constraints:", col_constraints)
    print()
    print("sub_box_constraints:", sub_box_constraints)
    print()
    print("########################################")

    # create solver
    s = z3.Solver()
    s.add(elem_constraints)
    s.add(val_constraints)
    s.add(row_constraints)
    s.add(col_constraints)
    s.add(sub_box_constraints)

    if(s.check() == z3.sat):
        model = s.model()
        solution = [[model.evaluate(plain_grid[row][col]) for row in range(0, 9, 1)] for col in range(0, 9, 1)] # for each z3,Int in model  index it for the value. get one elem at a time to get each row and put it in a list and repeat for each row
        print("Solution: ")
        for i in range(0, 9, 1):
            if i == 3 or i == 6 or i == 9:
                print("---------------------------------")
            print(solution[i])

if __name__ == "__main__":
    preset_sudoku()
