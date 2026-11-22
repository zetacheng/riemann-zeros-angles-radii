# Step 4(b): four ways to buy multiplicity, side by side

*Written by Claude (Anthropic, Claude Opus 5.5) at the request of Zeta Hoi-Ho Cheng, 22 November 2026.*

Part (a) found that a theta lift **appends a block** of Frobenius eigenvalues, so the cost in dimension is additive. It also warned that a block of powers of p, taken alone, gives no net gain, because of the product formula. Part (b) tests both statements in toy engines and asks what else is needed.

Script: `scripts/step4_engines.py`. Output: `validation/step4_engines.json` and `explorations/step4/engines.png`.

## Measure

Every engine bounds a counted quantity by "size ÷ multiplicity". The quantity reported is the **bound divided by the true value**, as a function of the multiplicity parameter. If it falls, multiplicity is being bought cheaply enough to help. E1 bounds nothing, so for it we show the cost per unit of multiplicity, normalised to 1 at the first step.

## Results

**E1. ℤ, Frobenius-type iteration.** N_j = 2^{3·7^j} − 1 has v₇ = 1 + j. Normalised cost per unit of multiplicity: 1, 3.5, 16.3, 85.8, 480, 2801, 16807. This is exponential, as in step 3 (C).

**E2. ℤ, a block of Tate twists at a single prime.** For N = ∏_{c<h} p^c and every p and h tested (p = 3, 7, 11; h = 2, 5, 10), v_p(N)·log p − log N = 0 exactly. The block costs exactly what it gains, so the warning in (a) holds.

**E3. ℤ, appended binomial blocks.** N_M = (Mn)!/(n!)^M = ∏_{j≤M} C(jn, n) with n = 1000. Each prime in (n, 2n] divides N_M at least μ_M times, so θ(2n) − θ(n) ≤ log N_M / μ_M. The true value is 983.6.

| M | μ_M (min multiplicity) | cost per block, log N_M / M | bound | bound / true |
|---|---|---|---|---|
| 2 | 1 | 691 | 1382 | 1.41 (Chebyshev) |
| 4 | 2 | 1383 | 2766 | 2.81 |
| 16 | 8 | 2769 | 5537 | 5.63 |
| 128 | 64 | 4848 | 9695 | 9.86 |

The multiplicity grows **linearly** (μ_M = M/2, at all 143 primes at once), and the chain is a chain of appended blocks. Yet the bound gets **worse**, roughly like log M. The cause is the cost of each new block, about n·log j, which grows with j while the gain per block stays at about one unit of multiplicity at each prime.

**E4. 𝔽₄₀₁, Stepanov** (paper Table 10). The bound divided by the true count falls from 2.81 (M = 1) to 1.04 (M = 16). The cost per step is bounded.

**E5. The verified proof, as described by Zhang** (a model from a secondary source, not data). With errors x/m + m at x = 10⁶, the ratio falls to 2/√x = 0.002 at m ≈ √x = 1000 and rises after that.

## Reading

1. **Additive cost is necessary.** E1 fails because its cost multiplies.
2. **Additive cost is not sufficient.** E3 is additive, and its multiplicity is linear and uniform across every prime in the range, and it still fails. Each appended block must cost at most a **bounded** amount, small compared with the base cost, in the units of the counted quantity. In E3 the per-block cost grows like log j.
3. **Blocks at one prime give nothing (E2).** The gain must come from one object that is divisible at **many primes at once**, as in Chebyshev's C(2n, n), whose archimedean size is controlled by something other than those primes.
4. Together, these leave one requirement for the proof's engine. **Each theta lift must add divisibility at all the inert primes up to x at once, while the normalised archimedean size grows by at most a bounded amount per lift.** In Zhang's accounting the archimedean side is a base term of order x, paid once, plus a chain term m² (that is, m per lift), and dividing by the multiplicity ∝ m gives x/m + m. As far as we can tell, the bounded growth per lift is what the normalisation of periods supplies: the normalised operators are close to isometries (Zhang, Lemma 4.2), so a lift does not inflate size the way a binomial block does.

## What this does not show

The toys show that **linear multiplicity plus bounded cost per step** is the right requirement. They do not show that theta lifts meet it. Two things remain unexplained, as at the end of (a):
- the local computation that turns an appended block into divisibility of the period values at inert primes;
- the near-isometry that keeps the archimedean cost per lift bounded.

These belong to part (c). Neither is computable in a toy, and the second is, in our reading, the real expert core.

**On E5.** E5 is a picture of the claimed error budget. It is not evidence for it.
