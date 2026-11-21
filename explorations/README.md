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

`scripts/torus_closure.py` (now §13 of the paper) places each prime on its own circle: the line t ↦ (t log p / 2π mod 1) for p ≤ P on the torus (Bohr's lift). It finds the first time at which every coordinate lies within ε of an integer, which is an approximate common lattice. Output: `validation/torus_closure.json`.

| primes (k) | 2 | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|
| first near-closure t, ε = 0.1 | 45 | 1.6·10³ | 3.0·10⁴ | 3.4·10⁵ | 5.5·10⁷ | 1.0·10⁹ |

Each additional prime multiplies the waiting time by about 5.3 at ε = 0.1 and about 10.3 at ε = 0.05, close to the heuristic 1/(2ε). With ε = 0.1, the helix nearly closes on about 17 primes by height 3·10¹² (the verified range), while the approximate functional equation at that height involves about 56,000 primes (those up to √(T/2π)). An approximate common lattice therefore covers only logarithmically many primes, so Stepanov's first ingredient cannot be obtained by approximation. Near-closure times of this kind are the classical mechanism for large values of ζ(1+it) (Bohr–Landau); they give extreme values, not RH.

## One spiral arm per prime (the author's drawing)

`scripts/prime_spirals.py` (now §14, Figure 7) draws, at s = 1/2 + 14.1347i, the points p^{-ks} (k = 1, 2, …) for p ≤ 13, then adds the arms tip to tail over the primes up to 10⁵ (now `paper/figures/fig7_spirals.pdf`).

- The arms are not separate curves. p^{-us} = e^{-(u log p)s}, so every arm lies on the same logarithmic spiral e^{-x s}, and prime p occupies the points x = k log p on it. The spiral is the helix of §2 with radius e^{-x/2}. Over F_q every point would sit at a multiple of log q, a common lattice on the spiral; over ℤ the spacings log p are incommensurable.
- Each arm sums to the Euler factor −log(1 − p^{-s}), which converges. The sum over all arms converges at σ = 3/2, but on the critical line it winds outward without converging, which is why analytic continuation is needed.
- The arms become genuinely separate only when each prime's point is rotated by an extra angle, such as a character value χ(p) or a Satake angle. That is the picture for an L-function in a family, and averaging over the family rotates the arms independently.

## Rotating the arms: the family of Dirichlet characters mod q

`scripts/character_family.py` (now §15) rotates each prime's arm by χ(p) for every Dirichlet character χ mod q (q = 101, 1009 and 10007, at s = 1/2 + 14.1347i). It computes W_χ(P), the logarithm of the partial Euler product over p ≤ P, for P up to 10⁶. Outputs: `validation/character_family.json` and `paper/figures/fig8_family.pdf`.

- **Claude's prediction was wrong.** Claude expected the family mean square of |W_χ|² to leave the diagonal Σ1/p once P exceeds q, growing like the large-sieve worst case (1 + P/q). Instead it stays at the diagonal (ratio 0.94–1.09) up to P = 10⁴q. The twist p^{-it} already decorrelates the arms within each residue class, so the worst case of the large sieve is far from attained.
- What the average controls is the *typical* size, |W_χ|² ≈ Σ1/p ≈ log log P, a Gaussian picture of the kind in Selberg's central limit theorem. The largest member grows with the family: max_{χ≠1}|W_χ|² at P = 10⁶ is about 9, 14 and 22 for the three values of q. Averaging pins down most members, not each one.
- The trivial member (ζ) is the outlier, oscillating up to |W|² ≈ 22 because of the pole at s = 1, the known impurity. Rotating the arms by χ ≠ 1 removes it.
- An off-line zero at height γ with β = 1/2 + δ becomes visible only when P^δ exceeds about γ (§9), so none of these statistics can see one. Turning a family statement into a statement about one member requires an amplifier or a multiplicity-type mechanism.

## Amplification: from the family to one member

`scripts/amplifier.py` (now §15) bounds a single member χ₀ of the family mod q = 10007 (P = 10⁵, s = 1/2 + 14.1347i) by weighting the family with the amplifier A_χ = |Σ_{ℓ≤L} χ̄₀(ℓ)χ(ℓ)|². Outputs: `validation/amplifier.json` and `paper/figures/fig9_amplifier.pdf`.

- The gain over the trivial bound equals the number of amplifier primes while L < q, and grows more slowly beyond q. At L = 10⁵ the amplified bound is within a factor of 1.1 of the true value for the largest member and for ζ, and within 1.9 for a median member.
- **Caveat:** the amplified moment is computed here *exactly* from the known W_χ. A proof must estimate it from orthogonality alone, which is exact only while the products ℓ·p^k stay below q, roughly L·P < q. Every run here lies far outside that range. The experiment therefore shows what amplification could achieve if the off-diagonal terms behaved as they do numerically. The difficulty of the method lies in the gap between this numerical behaviour and what can be proved.

## Is the worst member an "impurity"? (author's question)

`scripts/worst_member.py` (now §16 of the paper) asks whether the growth of the largest |W_χ|² with the family size is a sign of a new impurity (an off-line zero) or ordinary extreme-value statistics. It uses the families mod q for eight primes q from 31 to 100003 (up to 10⁵ members), with P = 10⁵. Output: `validation/worst_member.json`.

| q | members | largest \|W\|² | random model | extreme-value D(ln N + γ) | largest / ln N |
|---|---|---|---|---|---|
| 101 | 99 | 10.3 | 9.5 | 13.8 | 2.25 |
| 1009 | 1007 | 15.1 | 16.4 | 21.1 | 2.18 |
| 10007 | 10005 | 20.4 | 29.9 | 27.7 | 2.22 |
| 100003 | 100001 | 28.2 | 31.3 | 34.4 | 2.45 |

The largest member grows like ln N (the ratio stays near 2.2). In every case but one it lies below the maximum of a random model with independent random rotations, and it always lies below the exponential extreme-value prediction. The upper tail is in fact thinner than exponential: the fraction above 5D is at most 0.003, against e⁻⁵ ≈ 0.0067. The growth is therefore what one expects from drawing more members, and no impurity is needed to explain it. An impurity would show instead as power-law growth P^δ in one particular member, which at these sizes would be invisible unless P^δ exceeded the height of the zero.

## A suspected impurity: Siegel zeros and small L(1, χ) (author's question)

`scripts/siegel_check.py` (now §16) computes L(1, (·/q)) for every odd prime q ≤ 20000 (2261 characters, tail error at most 0.037). Output: `validation/siegel_check.json`. A Siegel zero would make L(1, χ) abnormally small, of order (1 − β) log q, which is below 1/log q (about 0.1 here). The smallest value found is 0.2459, at q = 163, where class number one gives L(1, χ) = π/√163 = 0.2461. All other values are at least 0.26. The most "impurity-like" member is therefore a genuine extreme value with an arithmetic explanation (the last imaginary quadratic field of class number one), not an off-line zero. The data show no outlier beyond the ordinary extreme-value range. This does not, and cannot, prove that Siegel zeros do not exist.

## q = 163: does the class-number-one character leave an impurity-like trace? (author's question)

`scripts/q163.py` and `scripts/q163_zeros.py` (now §16, Figure 10) study χ = (·/163). Outputs: `validation/q163.json` and `validation/q163_zeros.json`; the figure is `paper/figures/fig10_q163.pdf`.

- **Small primes conspire.** Every prime below 41 is inert (χ(p) = −1), and 41 is the first split prime. This is the arithmetic behind the small value L(1, χ) = π/√163.
- **No Siegel zero.** For x < 41, ψ(x, χ)/x sits near −0.4 to −0.8, as a real zero near 1 would produce. After 41 it collapses: it is −0.088 at x = 10³ and +0.002 at x = 3·10⁶, while a Siegel model with β = 0.99 would still give about −0.87. L(σ, χ) is positive on [1/2, 1) (minimum 0.068 near σ = 0.55).
- **But the lowest zero is anomalously low.** Λ(1/2 + it) is real; its first sign change for q = 163 is at t = 0.2029. For the nine neighbouring primes q ≡ 3 (mod 4) between 131 and 223 the first zero lies between 0.79 and 1.66, and Λ(1/2) is 1.6 for 163 against 25 to 149 for the others. The pair of zeros 1/2 ± 0.203i lies on the critical line, very close to the central point s = 1/2. In the α-plane they sit on the circle next to the positive real axis, where the known impurities lie.
- **This pair produces a slow drift.** It contributes about −2 Re(x^{iγ}/ρ)·√x to ψ(x, χ), an oscillation of amplitude 2/|ρ| ≈ 3.7 in ψ/√x, with period 2π/0.203 ≈ 31 in log x; one full cycle ends near x ≈ 3·10¹³. Over x ≤ 3·10⁶ this looks like a steady trend from −4.4 to +3.7, and the predicted values (−3.5, −2.0, −0.3, 1.4, 2.8, 3.3 at x = 40, 10³, …, 3·10⁶) follow the observed ones (−4.4, −2.8, −1.3, 0.8, 2.3, 3.7). It is a "false impurity" in the author's sense: an effect so slow that it looks like gradual worsening. It stays bounded relative to √x, unlike a genuine off-line zero, whose contribution would grow like x^δ√x.

**Literature check (2026-11-21).** The low zero of L(s, (·/163)) and its effect are known. Bays, Ford, Hudson and Rubinstein, *Zeros of Dirichlet L-functions near the real axis and Chebyshev's bias* (J. Number Theory 87 (2001), 54–76), give the first zero near 1/2 + 0.2029i. They explain it by the Chowla–Selberg formula: for class-number-one discriminants the leading term dominates, and −163 is the extreme case. They also show that the long quasi-period, about 31 in log x, makes the non-residue–residue prime race mod 163 negative for over 93% of integers below 10¹⁰, unlike every other modulus below 500. Our q = 163 observations are therefore a rediscovery of known results, with no priority claim.
