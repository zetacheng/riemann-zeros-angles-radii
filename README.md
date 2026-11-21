# Angles and Radii of the Riemann Zeros

**The circle as the answer, and the routes to it** · Zeta Hoi-Ho Cheng · Version 14, 21 November 2026

[Paper (PDF)](paper/Angles_and_Radii_of_the_Riemann_Zeros.pdf) · [LaTeX source](paper/Angles_and_Radii_of_the_Riemann_Zeros.tex)

## Scope

This is an expository and numerical paper. Every theoretical statement in it is classical. **It claims no new theorem and no progress toward the Riemann Hypothesis.** Its purpose is a reproducible, unified presentation of which properties of the zeros carry arithmetic information and which carry the content of the Riemann Hypothesis.

## The picture

Write a nontrivial zero as ρ = β + iγ and map it to α = b^ρ. The height γ becomes an **angle**, the real part β becomes a **radius**, and the Riemann Hypothesis says that every image lies on the circle |α| = √b.

| Finding | Where |
|---|---|
| A smoothed sum over the first 1200 zeros has peaks only at t = log n for prime powers n. The peak heights match the explicit-formula prediction to 0.01. | §3, Table 1 |
| Jittering the heights destroys the prime structure. Moving every zero off the line by up to δ = 0.49 keeps every peak in place and only rescales amplitudes by cosh(δt). | §4, Table 2 |
| The smooth background equals the pole term plus the archimedean term to within 0.002. In the α-plane the poles s = 0, 1 form a pair reflected across the circle, the same form an off-line zero pair would have. | §6, Table 4, Figure 4 |
| The projected angles fill the circle uniformly (Hlawka), but the prime bias and the eigenvalue repulsion are lost in the limit. | §7, Tables 5–6 |
| A truncated Weil quadratic form computed from primes alone is positive in every case tested. Using only the primes up to 11, its ground state recovers the first five ordinates of ζ to twelve digits, and at fixed support its computed smallest eigenvalue decays rapidly towards 0 (a numerical observation, not a proved absence of a spectral gap). | §8, Tables 7–8 |
| Turning the circle n times (α ↦ αⁿ) on an elliptic curve over F₇, where Frobenius exists, keeps the normalised radius at 1. A pair of off-circle roots gives "point counts" that are positive integers with all the divisibility relations of a curve; turning reveals it only relative to an a priori bound O(q^{n/2}), which must come from geometry. For ζ the analogue is ψ(2ⁿ) − 2ⁿ. | §9, Table 9, Figure 5 |
| Stepanov's method carried out for y² = x³ + x + 1 over F₄₀₁: an auxiliary polynomial fixed by linear conditions that do not depend on the number of points vanishes to order M at all 215 of them; the bound falls from 603 (M = 1) to 224 (M = 16). Verified directly for p ≤ 401 only; the general bound is Stepanov's theorem. The multiplicity M is the parameter that reaches the circle. | §10, Table 10, Figure 6 |
| The recursion behind the announced quasi-Riemann bound 0.874957… (Liu, arXiv:2610.12234), reproduced from its stated formulas: one step from the trivial bound reaches 0.87506, and the limit is fixed by a constant counting exponent 2/3, not by accumulated losses. | §11, Table 11, Figure 6 |
| One circle per prime (Bohr's lift): the first time the helix nearly closes on the first k primes grows by a factor of about 1/(2ε) per prime. By height 3·10¹², only about 17 primes close together, against about 56,000 that enter at that height. | §13, Table 13 |
| One spiral arm per prime: for ζ every arm lies on a single spiral, with p at the points k log p. The arms separate only when twisted by characters. | §14, Figure 7 |
| Arms rotated by Dirichlet characters: the family mean square stays at its diagonal far beyond the range that orthogonality guarantees, and an amplifier isolates one member to within 1.1× when the full family moments are computed numerically. This is empirical concentration, not an analytic bound. Orthogonality is exact, but it removes the congruence off-diagonal terms only for L·P < q; bounding them beyond that range is the open problem, which resembles the gap at which the quasi-Riemann method stops. | §15, Tables 14–15, Figures 8–9 |
| Apparent impurities tested. In a finite-sample comparison, the worst member of a family grows roughly like ln N, consistent with an extreme-value heuristic. The smallest L(1, χ) for prime q ≤ 20000 is at q = 163 (class number one). There an anomalously low zero (0.2029) produces a slow wave that looks like a trend. This is known (Bays–Ford–Hudson–Rubinstein 2001); we make no priority claim. | §16, Table 16, Figure 10 |
| A critical point. Counting sign changes forces every zero up to T = 1500 onto the circle, but only up to T. Under the heat flow, close pairs collide ever nearer to t = 0, with no slowing (no buffer; a buffer would contradict Rodgers–Tao, Λ ≥ 0). The Lee–Yang theorem, reproduced for a 4×4 Ising model, shows the exact structural "hard wall" that would be needed: palindromic symmetry alone fails, ferromagnetism succeeds. | §17, Tables 17–18, Figures 11–12 |
| Postscript: Alpöge's Lean-formalised proof was certified by the Lean FRO and the Mathlib Initiative on 21 Nov 2026. Read through an unsigned architecture guide, it passes our sticking points with positive-weight families and one-sided bounds (no off-diagonal estimate), multiplicity from divisibility of iterated theta lifts, Bost's slope inequality and a cyclotomic tower. It uses no Weil positivity and no spectral operator. The table records what this note got right and what it got wrong. | §19, Table 19 |

**Structure and conclusion.** The picture α = b^ρ, with every point on the circle, is taken as the answer. Part I (§2–7) studies what it encodes: the helix (the critical line with its heights) carries the arithmetic, and the circle carries the shape. Part II (§8–11) follows the two known routes from the primes to the circle as far as computation allows: positivity holds but, numerically, with no margin; the amplitude route needs a uniform bound with a constant loss, which Frobenius supplies through Stepanov's multiplicity and which the quasi-Riemann method, lacking such a parameter, cannot reach. Part III (§12) states what an operation equivalent to α = b^ρ would need: input from the primes alone, a spectrum that for ℤ, within the Frobenius analogy, would naturally come from a flow rather than a single map, and a structure that forces the spectrum onto the circle. Part IV (§13–18) explores a route of our own, starting from the author's pictures (one circle per prime, one spiral arm per prime). It converges on the structure of the quasi-Riemann method: numerically, the cross terms cancel far beyond what can be proved. The paper locates this gap; it does not fill it. A postscript (§19) compares it with the architecture of the formally verified proof.

## Related work

The off-line experiment of §4 was anticipated by Sakhr, Bhaduri and van Zyl, *Phys. Rev. E* 68 (2003) 026206. The angle bias of §5 is a special case of work by Ford and Zaharescu (2005) and coauthors. The computation of §8 follows the programme of Connes, Consani and Moscovici (arXiv:2310.18423, arXiv:2511.22755); a rigorously certified treatment of related truncations is given by Groskin (arXiv:2607.02828). Full references are in the paper.

## Reproducing everything

Requirements: Python 3 with `numpy`, `scipy`, `matplotlib` and `mpmath`, plus a LaTeX installation with `latexmk`.

```bash
cd scripts
./run_all.sh
```

This regenerates every number, table and figure and recompiles the paper. It takes about an hour, most of it for `torus_closure.py` and `turing_count.py`. All randomness uses a fixed seed (0). A clean run reproduces the stored outputs in `validation/` exactly.

| Script | Produces |
|---|---|
| `experiments.py` | Figures 1–3, Tables 2–3, `validation/results.json`. Recomputes the zeros with `mpmath.zetazero` if `data/zeros_1200.json` is missing (about 3 minutes). |
| `peak_heights.py` | Table 1 |
| `impurities_and_circle.py` | Tables 4–6, Figure 4 |
| `weil_form_mp.py L N dps` | Truncated Weil form from primes alone (Tables 7–8) |
| `weil_form_zero_side.py L N` | The same matrix built from the zeros, as an independent check |
| `frobenius_turns.py` | Table 9, Figure 5, `validation/frobenius_turns.json` |
| `stepanov.py p M J K`, `stepanov_sweep.py` | Table 10, `validation/stepanov_results.json` (the sweep takes about 6 minutes) |
| `quasi_rh_recursion.py` | Table 11, `validation/quasi_rh_recursion.json` |
| `fig6_routes.py` | Figure 6 |
| `torus_closure.py` | Table 13, `validation/torus_closure.json` (about 20 minutes) |
| `prime_spirals.py` | Figure 7 |
| `character_family.py` | Table 14, Figure 8, `validation/character_family.json` |
| `amplifier.py` | Table 15, Figure 9, `validation/amplifier.json` |
| `worst_member.py`, `siegel_check.py` | Table 16, smallest L(1, χ) |
| `q163.py`, `q163_zeros.py`, `fig10_q163.py` | §16, Figure 10 |
| `turing_count.py` | Table 17 (about 16 minutes) |
| `heat_flow_spacing.py`, `phase_transition.py`, `latent_heat.py` | §17, Figure 11 |
| `lee_yang.py` | Table 18, Figure 12 |

## Limitations

- The zeros come from `mpmath.zetazero`, which searches on the critical line. That they all lie on the line in this range follows from published verifications (Platt–Trudgian, up to 3·10¹²), not from this computation.
- The off-line experiment manipulates the zero set formally. It does not describe any L-function.
- The Weil-form computations use high-precision floating point checked by raising the precision. They are **not interval-certified**.
- §11 reproduces the quasi-Riemann recursion from the formulas stated in the cited preprint and checks their internal consistency; it does not verify the analytic estimates behind them. The quasi-Riemann and Alpöge announcements were unrefereed at the time of writing, and nothing in the paper depends on them.
- Part IV is exploratory. Its family and amplifier computations evaluate moments exactly at a single height, far outside the ranges usable in a proof.

## Collaboration

This research is a collaboration between the author and two AI systems:

| Contributor | Role |
|---|---|
| **Zeta Hoi-Ho Cheng** (author) | Research questions, the geometric picture of zeros on a circle, scope decisions |
| **Claude** (Anthropic; Claude Opus 5.5 as configured in the working sessions) | Computations, scripts, drafting and revisions |
| **ChatGPT** (OpenAI) | Independent review of successive versions; its reviews drove the corrections in versions 2 and 4 |

The author's original contributions — the zeros-on-a-circle picture, running the operation backwards, the impurities, the helix–circle synthesis and others — are listed item by item, with the sections they led to, in the paper's **Author contributions** paragraph. A fuller running record of who proposed what, including directions that were dropped or corrected, is kept in [CONTRIBUTIONS_LOG.md](CONTRIBUTIONS_LOG.md).

Neither AI system is listed as an author of the paper, in line with arXiv and journal policies. The author is responsible for the content. See [CONTRIBUTING.md](CONTRIBUTING.md) for how each contributor's work is recorded in this repository.
