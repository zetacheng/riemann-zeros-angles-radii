# Explorations

Working experiments that are not (yet) part of the paper.

- `theta_modular.py`: evaluates the Jacobi theta function theta3(x+iy) directly and by modular reduction (tau -> tau+1, tau -> -1/tau, tracking theta2/3/4 and the multipliers sqrt(-i tau)). Shows how the modular transformation computes the size of a long oscillating sum.
- `scan_theta.py`: size of theta3(x+iy) against the effective length N = 1/sqrt(y). Rational x = a/q (q even) give about N/sqrt(q); badly approximable irrationals give about sqrt(N), i.e. square-root cancellation, with each modular step contributing a factor of the golden ratio for x = (sqrt5-1)/2.
- `cubic_gauss_sums.py X`: cubic Gauss sums g(pi) at primary primes pi of Z[omega] with N(pi) <= X, the coefficients behind Kubota's cubic theta function. Checks |g|^2 = p and the classical identity g(pi)^3 = p*pi (both to about 1e-15), and studies the angles of g/sqrt(p). Up to X = 10^5 (9568 primes) the angles are visibly biased toward 0 (Kummer's 1846 observation), and the partial sums of g/sqrt(p) track X^(5/6)/log X (ratio 0.98-1.16 over a 16-fold range) rather than the random-walk size sqrt(count), as predicted by Patterson's conjecture (proved by Dunn and Radziwill, Annals 200 (2024), conditional on GRH for Hecke L-functions over Q(omega)). Outputs: `cubic_gauss_X20000.json`, `cubic_gauss_X100000.json`.

## Stage A: Stepanov's method, carried out explicitly

`stepanov.py p M J K` builds Stepanov's auxiliary polynomial for y² = x³ + x + 1 over F_p and verifies, point by point, that it vanishes to order M on every x with f(x) a nonzero square. `stepanov_sweep.py` writes `stepanov_results.json`.

Bound on |S| (true value 215) for p = 401 as the multiplicity M grows:

| M | 1 | 2 | 4 | 8 | 12 | 16 |
|---|---|---|---|---|---|---|
| equations / unknowns | 2 / 4 | 12 / 16 | 72 / 78 | 480 / 490 | 1512 / 1526 | 3456 / 3474 |
| bound deg R / M | 603 | 304.5 | 255.5 | 232.5 | 226.2 | 224.0 |

The number of equations never depends on |S|, yet R vanishes to order M at all 215 points (3440 conditions at M = 16). Without multiplicity (M = 1) the bound is worse than the trivial |S| ≤ p. The excess of the bound over p/2 grows like about 2.5√p (predicted from the parameter count for p up to 10⁵), which is the square-root bound. Frobenius enters twice: X^{pj} = X^j on F_p, and d/dX X^{pj} = 0 in characteristic p.
