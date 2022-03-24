from z3 import *

"""
    * @brief Solve a kinematic equation problem as an example of real z3 and constraint programming usage

    * Ima Hurryin is approaching the traffic lights at a velocity of 30m/s (meters per second).
    * The lights turns amber, so Ima applies the brakes to stop.
    * Q: If Ima’s acceleration is −8m/s2, then determine the displacement of the car during the skidding process.
"""

d, a, t, v_i, v_f = Reals('d a t v_i v_f')

# General Kinematic Equations
KEquations = [
   d == v_i * t + (a * t**2) / 2,
   v_f == v_i + a * t,
]
print("Kinematic Equations:")
print(KEquations)

# Specifics to this problem
constraints = [
    v_i == 30,
    v_f == 0,
    a   == -8
]
print("Constraints specific to this problem:")
print(constraints)

print("Solution:")
solve(KEquations + constraints)
