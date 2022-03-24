"""
    * @brief File shows has z3 can manipute bit vectors

    * One of the most common applications of z3 is verification of software and hardware

    * Since CPU's perform arithmetic with bit-vectors of a fixed size, z3 supports this and has a constructor and functionality for such objects both unsigned and two's complement signed

    * Bit vector constructors
          * BitVecVal is the constructor for bit vectors where value is known
            * Takes two params:
                * #1 value to be stored in bit vector
                * #2 size of bit vector (16 bits, 32 bits, etc.)
         * BitVec is the constructor for bit vectors where value is known
            * Takes two params:
                * #1 a string (if contents are unknown)
                * #2 size of bit vector (16 bits, 32 bits, etc.)


    * Since there are no distinction is datatype between signed and unsigned bit vectors, Z3 provides different operators which correspond to the signedness
        * Signed operators: <, <=, >, >=, /, %, >>
        * Unsigned functions: ULT (larger than), ULE (less or equal to), UGT (greater than), UGE (greator or equal to), UDiv (division), URem (modulo), LShR (right shift)
        * Shared bit-wise boolean logic operators: & (and), | (or), ~ (not)
        * Also == and != are still valid

"""

import z3


"""
    * @brief test_opposite_signs - test to see if a shorthand way of seeing if two given machine integers have opposite signedness
    * Shorthand: x ^ y < 0
        * ... where ^ is binary XOR in python
"""
def power_of_two_test():
    x = z3.BitVec("x", 32) # generic (unknown value) 32 bit vector
    y = z3.BitVec("y", 32) # generic (unknown value) 32 bit vector

    claim = x^y < 0 # create claim as formula

    print("Shorthand claim:", claim)

    manual = z3.Or(z3.And(x < 0, y >= 0), z3.And(x >= 0, y < 0)) # formal way to ascertain different signedness

    print("Manual:", manual)

    print("\nCan we prove they are equivalent?: ", end="")
    z3.prove(claim == manual) # Note that we used the function `prove` from earlier rather than `solve` - this is so we can VERIFY such that Z3 doesn’t just find one x / y pair which makes it work



if __name__ == "__main__":
    power_of_two_test()
