# Step 2 of a human path: what the one-sided bound must achieve

*Written by Claude (Anthropic, Claude Opus 5.5) at the request of Zeta Hoi-Ho Cheng, 21 November 2026.*

Step 1 reduced GRH for the characters mod q to the one-sided bound

$$E_q(x)=x-\varphi(q)\,\psi(x;q,1)\le C\,x^{\theta}\qquad(x\ge x_0)\tag{$\star_\theta$}$$

for every θ > 1/2. This step measures what the bound has to absorb on real data. It also sets out the exponent arithmetic that a Stepanov-type engine must satisfy. Script: `scripts/what_star_needs.py`; output: `validation/what_star_needs.json`.

## 1. ε > 0 is necessary, and enough

By Littlewood's theorem, ψ(x) − x takes values of size √x·log log log x of both signs, so $E_1(x)/\sqrt x$ is unbounded. A bound with θ = 1/2 exactly is therefore false, and the target has to be θ = 1/2 + ε for every ε > 0. That is exactly the form of the verified proof as described in the guide: exponent 1/2 + 9ε for each ε, with ε chosen after the putative zero.

## 2. Size on real data (x ≤ 5·10⁶)

| q | members φ(q) | max E_q/√x | min E_q/√x | C needed, θ = 0.55 | C needed, θ = 0.6 |
|---|---|---|---|---|---|
| 1 (ζ) | 1 | 0.67 | −0.69 | 0.47 | 0.33 |
| 5 | 4 | 2.38 | −2.26 | 1.21 | 0.82 |
| 11 | 10 | 5.65 | −5.39 | 3.86 | 2.64 |
| 19 | 18 | 16.2 | −3.9 | 10.4 | 6.7 |
| 31 | 30 | 18.6 | −11.6 | 10.7 | 7.1 |
| 47 | 46 | 22.3 | −19.4 | 10.9 | 6.0 |

Over the primes q ≤ 47 the maximum of E_q/√x grows roughly like φ(q)^0.84. So the constant in ($\star_\theta$) must be allowed to depend on q. A proof of GRH for all Dirichlet L-functions needs control of this dependence, that is, uniformity in the conductor, as well as of the exponent. These are finite-range values, not suprema.

## 3. Localised windows (q = 5)

In each window [Y, Y^1.2] (on a log scale, Y from 10³) the statistic reaches between +1.8 and +2.2 times √x, and dips below −1 times √x. A localised one-sided bound, the form the guide attributes to the verified proof, must therefore allow a few √x in **every** window. An off-line zero, by contrast, would exceed any C x^{1/2+ε} in every late window (step 1, `positivity_by_design.py`).

## 4. Exponent arithmetic of the engine

According to the guide, the engine yields error terms of the shape x/m + m + √x for a chain of m iterated theta lifts, optimised at m ≍ √x. For a chain whose cost grew like m^a instead, balancing x/m against m^a gives m = x^{1/(a+1)} and the exponent

$$\theta=\max\Bigl(\frac a{a+1},\ \frac12\Bigr).$$

| cost of a chain of length m | best m | exponent reached |
|---|---|---|
| m^{1/2} | x^{2/3} | 1/2 (√x term dominates) |
| m | x^{1/2} | **1/2** |
| m^{3/2} | x^{2/5} | 3/5 |
| m² | x^{1/3} | **2/3** |
| m³ | x^{1/4} | 3/4 |

The engine reaches the target only if a chain of length m costs no more than about m. Alpöge's note mentions that a naive version stops at a barrier of 2/3. One simple way such a barrier arises is a chain whose cost is quadratic in m. **This is our heuristic reading, not something the sources state.**

## 5. The ladder of exponents

| method | exponent θ in ($\star_\theta$), or the equivalent zero-free half-plane |
|---|---|
| classical unconditional (de la Vallée Poussin, Siegel–Walfisz) | θ = 1, saving only exp(−c√log x) |
| announced quasi-Riemann bound (OpenAI; Liu) | 0.874957 |
| verified proof, as described | 1/2 + 9ε for every ε |
| needed | 1/2 + ε for every ε |

## Conclusion of step 2

The target is precise. It is a **one-sided** bound with exponent 1/2 + ε for every ε > 0, a constant that may depend on q (growing roughly like φ(q)^0.84 in our range), and room for a few √x in every window. An engine meets it exactly when its chain costs grow linearly in the chain length. Step 3 will build toy versions of the two engine parts that can be computed: multiplicity from divisibility, and degree from a slope inequality.
