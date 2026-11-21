# Angles and Radii of the Riemann Zeros

**The circle as the answer, and the routes to it** · Zeta Hoi-Ho Cheng · Version 9, 21 November 2026

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

**Structure and conclusion.** The picture α = b^ρ, with every point on the circle, is taken as the answer. Part I (§2–7) studies what it encodes: the helix (the critical line with its heights) carries the arithmetic, and the circle carries the shape. Part II (§8–11) follows the two known routes from the primes to the circle as far as computation allows: positivity holds but, numerically, with no margin; the amplitude route needs a uniform bound with a constant loss, which Frobenius supplies through Stepanov's multiplicity and which the quasi-Riemann method, lacking such a parameter, cannot reach. Part III (§12) states what an operation equivalent to α = b^ρ would need: input from the primes alone, a spectrum that for ℤ, within the Frobenius analogy, would naturally come from a flow rather than a single map, and a structure that forces the spectrum onto the circle. The paper locates this gap; it does not fill it.

## Related work

The off-line experiment of §4 was anticipated by Sakhr, Bhaduri and van Zyl, *Phys. Rev. E* 68 (2003) 026206. The angle bias of §5 is a special case of work by Ford and Zaharescu (2005) and coauthors. The computation of §8 follows the programme of Connes, Consani and Moscovici (arXiv:2310.18423, arXiv:2511.22755); a rigorously certified treatment of related truncations is given by Groskin (arXiv:2607.02828). Full references are in the paper.

## Reproducing everything

Requirements: Python 3 with `numpy`, `scipy`, `matplotlib` and `mpmath`, plus a LaTeX installation with `latexmk`.

```bash
cd scripts
./run_all.sh
```

This regenerates every number, table and figure and recompiles the paper. It takes about eight minutes. All randomness uses a fixed seed (0). A clean run reproduces the stored outputs in `validation/` exactly.

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

## Limitations

- The zeros come from `mpmath.zetazero`, which searches on the critical line. That they all lie on the line in this range follows from published verifications (Platt–Trudgian, up to 3·10¹²), not from this computation.
- The off-line experiment manipulates the zero set formally. It does not describe any L-function.
- The Weil-form computations use high-precision floating point checked by raising the precision. They are **not interval-certified**.
- §11 reproduces the quasi-Riemann recursion from the formulas stated in the cited preprint and checks their internal consistency; it does not verify the analytic estimates behind them. The quasi-Riemann and Alpöge announcements were unrefereed at the time of writing, and nothing in the paper depends on them.

## Collaboration

This research is a collaboration between the author and two AI systems:

| Contributor | Role |
|---|---|
| **Zeta Hoi-Ho Cheng** (author) | Research questions, the geometric picture of zeros on a circle, scope decisions |
| **Claude** (Anthropic; Claude Opus 5.5 as configured in the working sessions) | Computations, scripts, drafting and revisions |
| **ChatGPT** (OpenAI) | Independent review of successive versions; its reviews drove the corrections in versions 2 and 4 |

The author's original contributions — the zeros-on-a-circle picture, running the operation backwards, the impurities, the helix–circle synthesis and others — are listed item by item, with the sections they led to, in the paper's **Author contributions** paragraph.

Neither AI system is listed as an author of the paper, in line with arXiv and journal policies. The author is responsible for the content. See [CONTRIBUTING.md](CONTRIBUTING.md) for how each contributor's work is recorded in this repository.
