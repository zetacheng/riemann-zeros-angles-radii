# Explorations

Working experiments that are not (yet) part of the paper.

- `theta_modular.py`: evaluates the Jacobi theta function theta3(x+iy) directly and by modular reduction (tau -> tau+1, tau -> -1/tau, tracking theta2/3/4 and the multipliers sqrt(-i tau)). Shows how the modular transformation computes the size of a long oscillating sum.
- `scan_theta.py`: size of theta3(x+iy) against the effective length N = 1/sqrt(y). Rational x = a/q (q even) give about N/sqrt(q); badly approximable irrationals give about sqrt(N), i.e. square-root cancellation, with each modular step contributing a factor of the golden ratio for x = (sqrt5-1)/2.
