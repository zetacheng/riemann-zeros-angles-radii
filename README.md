# Angles and Radii of the Riemann Zeros

**A numerical study of the zeros of ζ as a discrete spectrum** · Zeta Hoi-Ho Cheng · Version 6, 20 November 2026

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
| A truncated Weil quadratic form computed from primes alone is positive in every case tested. Using only the primes up to 11, its ground state recovers the first five ordinates of ζ to twelve digits, and at fixed support its smallest eigenvalue tends to 0. | §8, Tables 7–8 |

**Conclusion of the paper:** the helix (the critical line with its heights) carries the arithmetic, and the circle carries the shape asserted by the Riemann Hypothesis. A proof needs a bridge from one to the other. Weil positivity is such a bridge, and §8 shows numerically why it is delicate: it holds, but with no margin.

## Related work

The off-line experiment of §4 was anticipated by Sakhr, Bhaduri and van Zyl, *Phys. Rev. E* 68 (2003) 026206. The angle bias of §5 is a special case of work by Ford and Zaharescu (2005) and coauthors. The computation of §8 follows the programme of Connes, Consani and Moscovici (arXiv:2310.18423, arXiv:2511.22755); a rigorously certified treatment of related truncations is given by Groskin (arXiv:2607.02828). Full references are in the paper.

## Reproducing everything

Requirements: Python 3 with `numpy`, `scipy`, `matplotlib` and `mpmath`, plus a LaTeX installation with `latexmk`.

```bash
cd scripts
./run_all.sh
```

This regenerates every number, table and figure and recompiles the paper. It takes about two minutes. All randomness uses a fixed seed (0). A clean run reproduces the stored outputs in `validation/` exactly.

| Script | Produces |
|---|---|
| `experiments.py` | Figures 1–3, Tables 2–3, `validation/results.json`. Recomputes the zeros with `mpmath.zetazero` if `data/zeros_1200.json` is missing (about 3 minutes). |
| `peak_heights.py` | Table 1 |
| `impurities_and_circle.py` | Tables 4–6, Figure 4 |
| `weil_form_mp.py L N dps` | Truncated Weil form from primes alone (Tables 7–8) |
| `weil_form_zero_side.py L N` | The same matrix built from the zeros, as an independent check |

## Limitations

- The zeros come from `mpmath.zetazero`, which searches on the critical line. That they all lie on the line in this range follows from published verifications (Platt–Trudgian, up to 3·10¹²), not from this computation.
- The off-line experiment manipulates the zero set formally. It does not describe any L-function.
- The Weil-form computations use high-precision floating point checked by raising the precision. They are **not interval-certified**.

## Collaboration

This research is a collaboration between the author and two AI systems:

| Contributor | Role |
|---|---|
| **Zeta Hoi-Ho Cheng** (author) | Research questions, the geometric picture of zeros on a circle, scope decisions |
| **Claude** (Anthropic; Claude Opus 5.5 as configured in the working sessions) | Computations, scripts, drafting and revisions |
| **ChatGPT** (OpenAI) | Independent review of successive versions; its reviews drove the corrections in versions 2 and 4 |

Neither AI system is listed as an author of the paper, in line with arXiv and journal policies. The author is responsible for the content. See [CONTRIBUTING.md](CONTRIBUTING.md) for how each contributor's work is recorded in this repository.
