# Step 3 of a human path: toy versions of the engine

*Written by Claude (Anthropic, Claude Opus 5.5) at the request of Zeta Hoi-Ho Cheng, 21 November 2026.*

Stepanov's method over F_p (paper §10) used three things:

1. free linear algebra (any nonzero solution will do);
2. a degree that bounds the number of zeros;
3. multiplicity obtained cheaply, because d/dX of X^p is 0.

Step 2 showed what the number-field engine must deliver: errors x/m + m^a with a = 1, i.e. multiplicity at a cost linear in the chain length. This step computes toy versions of the replacements over ℤ and measures what each one costs. Script: `scripts/engine_toys.py`; output: `validation/engine_toys.json` and `paper/figures/fig14_engine.pdf`.

## (A) Linear algebra is not free over ℤ: Siegel's lemma

Over F_p any nonzero solution of the linear system works. Over ℤ the auxiliary object must also be **small**, because its size will play the role of degree. Siegel's lemma: a system A y = 0 with M equations, N > M unknowns and integer entries |a_ij| ≤ B has a nonzero integer solution with |y| ≤ (NB)^{M/(N−M)}. With LLL on random systems (B = 10):

| M | N | smallest solution found (median) | Siegel bound | exponent M/(N−M) |
|---|---|---|---|---|
| 2 | 6 | 1 | 8 | 0.5 |
| 3 | 9 | 2 | 9 | 0.5 |
| 4 | 12 | 2 | 11 | 0.5 |
| 2 | 4 | 8 | 40 | 1 |
| 4 | 8 | 8 | 80 | 1 |
| 6 | 12 | 7 | 120 | 1 |

The surplus of unknowns buys smallness. With twice as many unknowns as equations the cost exponent is 1, and with three times as many it is 1/2. This is the arithmetic counterpart of the "more unknowns than equations" step of §10, and it has a price that F_p did not charge.

## (B) Size replaces degree: the product formula

Over ℤ the statement "a polynomial of degree D has at most D roots" becomes "a nonzero integer has absolute value at least 1": if N ≠ 0 is divisible by many primes, it must be large. Chebyshev's argument is the simplest instance. C(2n, n) is divisible by every prime in (n, 2n] and is at most 4ⁿ, so θ(2n) − θ(n) ≤ n log 4.

| n | θ(2n) − θ(n) | log C(2n, n) | n log 4 | true ratio to n |
|---|---|---|---|---|
| 10³ | 983.6 | 1382.3 | 1386.3 | 0.984 |
| 10⁴ | 9909.3 | 13857.8 | 13862.9 | 0.991 |
| 10⁵ | 99833.6 | 138623.1 | 138629.4 | 0.998 |

The bound is one-sided and off only by a constant factor (log 4 ≈ 1.386 against the truth 1), the same kind of loss as in step 1. In higher rank, Bost's slope inequality is the sophisticated version of this principle. A Euclidean lattice has an Arakelov degree (minus the log of its covolume), and an injective map between lattices cannot raise degree beyond what the slopes of the target and the size of the map allow. According to the guide, this is what counts the zeros in the verified proof.

## (C) Multiplicity: exponential cost by iteration, bounded cost in Stepanov

Over ℤ the natural way to iterate "Frobenius" is to raise to the p-th power. The chain N_j = 2^{3·7^j} − 1 gains exactly one factor of 7 per step (lifting the exponent: v₇ = 1 + j), but its log-height is multiplied by 7 per step:

| step j | v₇(N_j) | log N_j | (gain · log 7)/(log N_j) |
|---|---|---|---|
| 0 | 1 | 2.1 | 0.94 |
| 2 | 3 | 101.9 | 0.057 |
| 4 | 5 | 4992.7 | 0.0019 |
| 6 | 7 | 244644 | 0.0001 |

The cost per unit of multiplicity grows exponentially. In Stepanov's construction over F_401 (paper Table 10), the cost per unit of multiplicity, deg R/M, *decreases* from 603 to 224 and levels off. Multiplicity there is cheap because X^{p} has zero derivative. This is the quantitative form of the sentence "ℤ has no Frobenius": the obvious iteration exists, but it is far too expensive.

## The human precedent: Diophantine approximation

A complete, human-readable instance of this engine over ℤ already exists. Approximating an algebraic number α of degree d by rationals p/q, the exponent μ in |α − p/q| > q^{−μ} came down a ladder:

| | exponent μ | ingredient added |
|---|---|---|
| Liouville (1844) | d | a nonzero integer is ≥ 1 |
| Thue (1909) | d/2 + 1 | an auxiliary polynomial in two variables, with multiplicity |
| Siegel (1921), Dyson (1947) | 2√d, √(2d) | optimised multiplicity |
| Roth (1955) | 2 + ε | many variables, with Roth's lemma controlling the multiplicity |

Roth's 2 + ε is optimal up to ε, as 1/2 + ε is for the Riemann Hypothesis, and it was reached by exactly the three ingredients above: Siegel's lemma, size in place of degree, and multiplicity bought cheaply enough. Each step on that ladder made the multiplicity cheaper. The structure is close to the ladder of step 2 (1 → 0.875 → 1/2 + ε). The analogy is ours; the guide does not mention Roth.

## Conclusion of step 3

(A) and (B) have working replacements over ℤ, Siegel's lemma and size or slope, with costs that are a constant or a power that can be controlled. (C) is the crux. Naive iteration over ℤ makes multiplicity exponentially expensive, while the target from step 2 needs it at linear cost. According to the guide, the verified proof obtains it from divisibility of m-fold iterated theta lifts, with errors x/m + m + √x, which is linear. How theta lifts achieve this is step 4, the expert core, and it cannot be reduced to a toy computation here.
