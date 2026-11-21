# Explorations

Working experiments that are not (yet) part of the paper.

- `theta_modular.py`: evaluates the Jacobi theta function theta3(x+iy) directly and by modular reduction (tau -> tau+1, tau -> -1/tau, tracking theta2/3/4 and the multipliers sqrt(-i tau)). Shows how the modular transformation computes the size of a long oscillating sum.
- `scan_theta.py`: size of theta3(x+iy) against the effective length N = 1/sqrt(y). Rational x = a/q (q even) give about N/sqrt(q); badly approximable irrationals give about sqrt(N), i.e. square-root cancellation, with each modular step contributing a factor of the golden ratio for x = (sqrt5-1)/2.
- `cubic_gauss_sums.py X`: cubic Gauss sums g(pi) at primary primes pi of Z[omega] with N(pi) <= X, the coefficients behind Kubota's cubic theta function. Checks |g|^2 = p and the classical identity g(pi)^3 = p*pi (both to about 1e-15), and studies the angles of g/sqrt(p). Up to X = 10^5 (9568 primes) the angles are visibly biased toward 0 (Kummer's 1846 observation), and the partial sums of g/sqrt(p) track X^(5/6)/log X (ratio 0.98-1.16 over a 16-fold range) rather than the random-walk size sqrt(count), as predicted by Patterson's conjecture (proved by Dunn and Radziwill, Annals 200 (2024), conditional on GRH for Hecke L-functions over Q(omega)). Outputs: `cubic_gauss_X20000.json`, `cubic_gauss_X100000.json`.
