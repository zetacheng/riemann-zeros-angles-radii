# Explorations

Working experiments that are not (yet) part of the paper.

- `theta_modular.py`: evaluates the Jacobi theta function theta3(x+iy) directly and by modular reduction (tau -> tau+1, tau -> -1/tau, tracking theta2/3/4 and the multipliers sqrt(-i tau)). Shows how the modular transformation computes the size of a long oscillating sum.
- `scan_theta.py`: size of theta3(x+iy) against the effective length N = 1/sqrt(y). Rational x = a/q (q even) give about N/sqrt(q); badly approximable irrationals give about sqrt(N), i.e. square-root cancellation, with each modular step contributing a factor of the golden ratio for x = (sqrt5-1)/2.
- `cubic_gauss_sums.py X`: cubic Gauss sums g(pi) at primary primes pi of Z[omega] with N(pi) <= X, the coefficients behind Kubota's cubic theta function. Checks |g|^2 = p and the classical identity g(pi)^3 = p*pi (both to about 1e-15), and studies the angles of g/sqrt(p). Up to X = 10^5 (9568 primes) the angles are visibly biased toward 0 (Kummer's 1846 observation), and the partial sums of g/sqrt(p) track X^(5/6)/log X (ratio 0.98-1.16 over a 16-fold range) rather than the random-walk size sqrt(count), as predicted by Patterson's conjecture (proved by Dunn and Radziwill, Annals 200 (2024), conditional on GRH for Hecke L-functions over Q(omega)). Outputs: `cubic_gauss_X20000.json`, `cubic_gauss_X100000.json`.

## Stage A: Stepanov's method, carried out explicitly

`scripts/stepanov.py p M J K` (moved to `scripts/` in version 8, now §10 of the paper) builds Stepanov's auxiliary polynomial for y² = x³ + x + 1 over F_p and verifies, point by point, that it vanishes to order M on every x with f(x) a nonzero square. `scripts/stepanov_sweep.py` writes `validation/stepanov_results.json`.

Bound on |S| (true value 215) for p = 401 as the multiplicity M grows:

| M | 1 | 2 | 4 | 8 | 12 | 16 |
|---|---|---|---|---|---|---|
| equations / unknowns | 2 / 4 | 12 / 16 | 72 / 78 | 480 / 490 | 1512 / 1526 | 3456 / 3474 |
| bound deg R / M | 603 | 304.5 | 255.5 | 232.5 | 226.2 | 224.0 |

The number of equations never depends on |S|, yet R vanishes to order M at all 215 points (3440 conditions at M = 16). Without multiplicity (M = 1) the bound is worse than the trivial |S| ≤ p. The excess of the bound over p/2 grows like about 2.5√p (predicted from the parameter count for p up to 10⁵), which is the square-root bound. Frobenius enters twice: X^{pj} = X^j on F_p, and d/dX X^{pj} = 0 in characteristic p.

## Stage B: the quasi-RH recursion

`scripts/quasi_rh_recursion.py` (now §11 of the paper) reproduces the length-optimisation recursion of B. Liu, *Improved zero-free half-planes for the quasi-Riemann hypothesis*, arXiv:2610.12234 (building on OpenAI's 7/8 argument), from the formulas stated there: κ = 2σ − 1, the critical-class equation (216κ−18)δ² − (468κ−57)δ + 150κ − 20 = 0 (counting exponent 2/3), and B(ξ) = (18ξ+7)/(18ξ+9). Output in `validation/quasi_rh_recursion.json`.

- The fixed point is B_new = 0.874957019420…, the root of 1188ξ³ − 2160ξ² + 171ξ + 190 = 0, as stated in the paper; B at κ = 3/4 reproduces B_alg = (1507 − 2√921)/1653.
- Starting from the trivial hypothesis σ = 1, one step already gives 0.87506. The sensitivity dB/dσ at the fixed point is 0.0012, and even the strongest moment input allowed (κ = 13/18) gives 0.87494. The barrier is therefore not an accumulation of losses: it is set by the critical counting exponent 2/3.
- The three constraints L₀, L_K, H_c with the stated weights combine to B ≥ (7+18δ_c)/(9+18δ_c), independently of the length parameters (checked).

Contrast with stage A: Stepanov's method has a parameter, the multiplicity M, that grows with p, and the bound improves without limit as it grows. This comparison system has no such parameter; its counting exponent is a fixed constant.

## Stage C, first experiment: how close does the helix come to closing?

`torus_closure.py` places each prime on its own circle: the line t ↦ (t log p / 2π mod 1) for p ≤ P on the torus (Bohr's lift). It finds the first time at which every coordinate lies within ε of an integer, which is an approximate common lattice. Output: `torus_closure.json`.

| primes (k) | 2 | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|
| first near-closure t, ε = 0.1 | 45 | 1.6·10³ | 3.0·10⁴ | 3.4·10⁵ | 5.5·10⁷ | 1.0·10⁹ |

Each additional prime multiplies the waiting time by about 5.3 at ε = 0.1 and about 10.3 at ε = 0.05, close to the heuristic 1/(2ε). With ε = 0.1, the helix nearly closes on about 17 primes by height 3·10¹² (the verified range), while the approximate functional equation at that height involves about 56,000 primes (those up to √(T/2π)). An approximate common lattice therefore covers only logarithmically many primes, so Stepanov's first ingredient cannot be obtained by approximation. Near-closure times of this kind are the classical mechanism for large values of ζ(1+it) (Bohr–Landau); they give extreme values, not RH.
