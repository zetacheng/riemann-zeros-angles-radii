# Contributions log

A running record of who proposed what in this research, so that the author's ideas, Claude's proposals and ChatGPT's reviews can be told apart later. The paper's **Author contributions** paragraph lists only the author's ideas that became sections. This log also records directions, decisions, questions and proposals that were dropped or corrected.

**How it is kept.** Claude adds entries whenever a new direction, idea or decision comes up in discussion. Every entry names its source:
- **Zeta**: the author (Zeta Hoi-Ho Cheng);
- **Claude**: Anthropic, Claude Opus 5.5 as configured in the working sessions;
- **ChatGPT**: OpenAI, as reviewer.

The *Outcome* column records what happened to each entry, including corrections.

> Entries up to 2026-11-21 were reconstructed on that date from the working sessions. Some of those records are summaries, so the wording is approximate and dates are given only to the day the discussion took place. Entries from 2026-11-21 onward are recorded as they happen.

## 1. Geometric picture (discussion that led to versions 1–6)

| # | Source | Idea, question or decision | Outcome |
|---|---|---|---|
| 1 | Zeta | Project the infinite real line onto a bounded segment and rotate it so that multiplication becomes a straight line, removing composites. | Became the Frobenius picture α = b^ρ (paper §2; Author contributions item 1). |
| 2 | Zeta | Go back to the starting point, where the earlier work went wrong, and restart from there. | Direction for the whole paper. |
| 3 | Zeta | The difficulty lies in analytic continuation: we look for a line, but the line is infinitely long. | Refined into the distinction between finite-scale and infinite-scale information and the Li circle (§2, §4; item 2). |
| 4 | Zeta | Infinitely many zeros mean the line "turns a full circle". This calls for a new operation whose output is a circle (not necessarily a round one). | The Frobenius picture and the "missing operation" theme (item 1; later Part III). |
| 5 | Claude | Formalise this as α = b^ρ: the angle is γ log b and the radius is b^β. Add the Li circle z = 1 − 1/ρ as a third picture. | §2. |
| 6 | Zeta | Asked what the missing "Frobenius" in number fields is. | Claude explained Weil numbers, Honda–Tate and Katz–Sarnak. |
| 7 | Zeta | Place the zeros on the circle and run the Frobenius operation backwards to see what domain comes out. | Became the reverse trace (§3; item 3). |
| 8 | Claude | Define the reverse trace R(t) and predict its peak heights from the explicit formula. | §3, Table 1. |
| 9 | Zeta | Conviction that the zeros must lie on the circumference. | Tested by the angle–radius experiment. Confirmed in one sense and refuted in another (§4; item 4, partly corrected). |
| 10 | Claude | Experiment: jitter the heights versus move the zeros off the line (δ up to 0.49). | §4, Table 2. Anticipated by Sakhr–Bhaduri–van Zyl (2003), now credited. |
| 11 | Zeta | The zeros form a "discrete circle with specific angles". Does a discrete-circle operator exist that would solve Hilbert–Pólya? | Claude: this is the Hilbert–Pólya problem itself, and it is open. The description is used in §5 and §12. |
| 12 | Zeta | The circle carries "impurities" that hold the key to the obstruction. Positivity means no impurities remain once the known ones are removed. RH means the impurities are exactly two points. | §6, Table 4, Figure 4 (item 5). |
| 13 | Zeta | Asked for a figure of the impurities. | Figure 4. |
| 14 | Zeta | Do infinitely many zeros fill the circle? Compared this with the rationals in the reals, and proposed the filled circle as the complete zero set. | §7 (item 6). Partly corrected: the filled circle loses the arithmetic. |
| 15 | Zeta | Synthesis: the helix carries the arithmetic but has no regular form; projecting it onto the circle gives a clear shape but erases the arithmetic. | Conclusion of the paper (item 7). |

## 2. Paper, repository and positivity route (versions 1–6)

| # | Source | Idea, question or decision | Outcome |
|---|---|---|---|
| 16 | Zeta | Write the observations up as a paper, check novelty and references, and open a public repository. | Versions 1–6 and this repository. |
| 17 | Zeta | Every commit must say who wrote it; credit the Claude–ChatGPT collaboration; add an Author contributions section. | CONTRIBUTING.md, commit trailers, Author contributions paragraph. |
| 18 | ChatGPT | Review of v1: the weights are not carried by the heights alone, the radius is not invisible at finite scale, the single-term dominance argument is only a heuristic, and the truncation error is unquantified. | Corrected in v2. |
| 19 | ChatGPT | Review of v3: the Weil test class, the status of the Poisson spacings, the finite-height Landau bias, and the description of peak positions. | Corrected in v4. |
| 20 | Claude | Distinguish two routes from primes to the circle: positivity (Weil, Connes) and amplitude (bounds on prime sums, as in Stepanov). | Framework for Part II. |
| 21 | Zeta | Alpöge took one route; we take the other. | The positivity route was computed (§8; item 8). |
| 22 | Claude | Compute a truncated Weil form from primes alone at high precision. | §8, Tables 7–8: positive, recovers five ordinates, no margin. |

## 3. Amplitude route (versions 7–9)

| # | Source | Idea, question or decision | Outcome |
|---|---|---|---|
| 23 | Zeta | The positivity route is probably a dead end, since many people, ourselves included, have walked it. | Decision to pursue the amplitude route. |
| 24 | Zeta | Try the amplitude route with a projection method: build the helix and project it onto the circle. | Claude advised against it, because projections retain only statistics. Not pursued. |
| 25 | Zeta | Try the theta modular transformation ourselves. | `explorations/theta_modular.py`. |
| 26 | Claude | Jacobi theta lacks arithmetic, so move to cubic Gauss sums (Kubota). | `explorations/cubic_gauss_sums.py`. |
| 27 | Zeta | Read the OpenAI quasi-RH preprint. Did it get stuck? How does it differ from Alpöge's method? | Comparison given in discussion. Claude's first account contained errors (entry 36). |
| 28 | Zeta | Run Frobenius backwards and turn the circle n times. | v7 §9, Table 9, Figure 5 (item 9). Claude showed that turning is only the last step of the route. |
| 29 | Claude | Off-circle example T² − 7T + 7: its counts are positive integers, yet its roots lie off the circle. | v7 §9. |
| 30 | Zeta | Asked what step 1 corresponds to in our picture, and why we cannot do it. | Claude: an operation of which the primes are fixed points; none is known for ℤ. |
| 31 | Zeta | Reformulation: start from the primes and create a new operation whose output is the circle (the zeros). | Basis of Part III (§12). |
| 32 | Zeta | Proposed the spike graph (reverse trace) as a starting point. | Claude: the spikes are prime data, and this leads back to Weil positivity, which §8 had already computed. Not in the paper. |
| 33 | Claude | Plan with three stages: A (Stepanov in the function field), B (the quasi-RH recursion), C (Alpöge, once readable). | Zeta chose to do A first, then B. |
| 34 | Claude | Construct Stepanov's auxiliary polynomial explicitly over F_p and verify it point by point. | §10, Table 10. |
| 35 | Claude | Reproduce the quasi-RH recursion from Liu (arXiv:2610.12234). | §11, Table 11. Finding: a fixed counting exponent of 2/3 sets the limit. |
| 36 | Claude | **Correction of Claude's own errors:** the quasi-RH limit was described as accumulating losses with a fixed point near 0.8745. | Wrong. The limit is 0.874957…, set by a constant. Corrected in v8. |
| 37 | Zeta | Since we no longer use α = b^ρ as a tool, the paper should be restructured, not extended. | Claude disagreed in part: α = b^ρ remains the descriptive language. |
| 38 | Zeta | α = b^ρ is the answer; stages A, B and C should end in something equivalent to it. | Three-part structure of v8 (item 10). |
| 39 | Claude | Within the Frobenius analogy, the object equivalent to α = b^ρ for ℤ should be a flow, not a single map. | §12. Qualified after ChatGPT's review (entry 40). |
| 40 | ChatGPT | Review of v8 (issue #1): the spectral gap is not proved; R ≠ 0 is not guaranteed for large p; the norm factorisation N_n = (1−Aⁿ)(1−Bⁿ); mark the quasi-RH bound as announced; present the flow as an analogy, not a necessity. | Six of seven points adopted in v9. The point about a missing label did not apply. |
| 41 | Zeta | Closed issue #1. Continue with stage C. Keep a record that separates the author's ideas from Claude's. | This log. |
| 42 | Zeta | For stage C, look for our own route instead of waiting for Alpöge's write-up, treating his result only as a sign of a more promising starting point. Asked what is missing, expressed in the paper's picture. | Discussion 2026-11-21: Claude located the gap in the incommensurability of the prime lengths log p (entry 43). |
| 43 | Claude | In the picture, Stepanov's engine needs all the counted points to be fixed points of one operation at once. Over F_q the spikes of the reverse trace lie on the lattice of multiples of log q. Over ℤ they sit at incommensurable lengths log p, which is the same reason the helix does not close into a circle. The degree bound and the free construction have number-field analogues (Jensen's formula, Siegel's lemma, as used in transcendence theory); the common-lattice property does not. | Proposed framing for stage C. |
| 44 | Zeta | The "discrete circle" fills the circle only in the limit; it looks like a circle and is not one. Pull the circle apart in another dimension and it becomes the helix. | Claude: one extra dimension gives exactly the helix of §2, which still does not close. Refined to one circle per prime, an infinite torus on which the helix becomes a straight line closing in each prime's own coordinate (Bohr's lift, Kronecker). Discussed 2026-11-21. |
| 45 | Claude | Experiment: the first time the helix nearly closes on the torus of the first k primes. | Waiting time grows by a factor of about 1/(2ε) per prime; at height 3·10¹² only about 17 primes close together, against about 56,000 needed. The approximate-lattice route is excluded quantitatively (`explorations/torus_closure.py`). |
| 46 | Zeta | Drawing: a spiral with one arm (line) per prime, all winding into a common centre. Is this direction 3, or the torus method? | Claude computed it (`explorations/prime_spirals.py`). For ζ every arm lies on one logarithmic spiral, with prime p at the points k log p. The arms separate only when twisted by characters or Satake angles, which is the family picture behind direction 3. Discussed 2026-11-21. |
| 47 | Claude | Experiment on direction 3: rotate the arms by Dirichlet characters mod q and average over the family. **Claude predicted** that averaging would control the arms only up to P ≈ q. | **The prediction was wrong.** The mean square stays at the diagonal up to P = 10⁴q. Averaging controls typical members (a Gaussian picture), the worst member grows with the family, and ζ's pole shows as the outlier. Family averaging alone cannot isolate one member; the next tool would be amplification (`explorations/character_family.py`). |
| 48 | Zeta | Run the amplifier experiment. Asked whether we are still on the right path, and closer to the quasi-RH work. | Claude: numerically the amplifier isolates one member almost perfectly, but only because the moments are computed exactly; provable estimates need L·P < q. Our route has converged on the structure of the quasi-RH method (family, moments, amplification, large sieve). That structure is viable, but it is the one that stops near 0.875, so being close to it is not yet progress (`explorations/amplifier.py`). |
| 49 | Zeta | Asked whether going further means reaching the place where quasi-RH is stuck. Decided to write up the stage-C work as Part IV of the paper. | Claude: broadly yes, the same class of obstacle (orthogonality is provable only in a limited range), though our experiments are cruder than that method. Version 10 adds Part IV (§13–16). |
| 50 | Zeta | Hypothesis: the growth of the worst member may be an "impurity". Perhaps impurities are not just the two initial ones: a third may appear somewhere, so slowly that it looks like gradual worsening, and too rare to see in the aggregate. | Tested by Claude (entry 51). The hypothesis that sparse impurities exist is logically legitimate and cannot be excluded by statistics; its best-known concrete form is a Siegel (exceptional) zero. |
| 51 | Claude | Experiment: largest member against an extreme-value model and a random model, for family sizes 29 to 10⁵. | The largest member grows like ln N and stays below the random-model maximum in every case but one, so no impurity is needed to explain it. An impurity would show as power-law growth in one member (`explorations/worst_member.py`). |
| 52 | Zeta | Perhaps the Siegel zero is a "false impurity": only suspected, in reality something like a case very close to an extreme value. | Claude: largely the expert view. A Siegel zero is equivalent in effect to L(1, χ) being abnormally small, so the suspicion lives in the extreme tail of L(1, χ), which proofs cannot yet control without GRH. Tested in entry 53. |
| 53 | Claude | Experiment: L(1, (·/q)) for all odd primes q ≤ 20000. | Smallest 0.2459 at q = 163 (class number one, π/√163), all others at least 0.26; no outlier near 1/log q. The most suspicious case is an arithmetically explained extreme value. Not a proof (`explorations/siegel_check.py`). |
| 54 | Zeta | Test whether q = 163 shows a faint impurity-like effect. | Claude's experiments (entry 55). |
| 55 | Claude | q = 163: prime sums, L on the real segment, and the lowest zeros against nine neighbouring moduli. | No Siegel zero: the early bias from small inert primes vanishes after 41. But the lowest zero (t = 0.2029) is anomalously close to s = 1/2 compared with the neighbours (0.79–1.66). This on-line pair produces a slow oscillation, with period about 31 in log x, that over x ≤ 3·10⁶ looks like a steady drift. This realises the author's "slow impurity" picture as a bounded, on-line effect. Whether the low zero is recorded in the literature was not checked (`explorations/q163*.py`). |
| 56 | Zeta | Check the literature on the q = 163 low zero. Asked whether the drift is a property of all ordinary zeros, each with a small effect that adds up over time. | Literature: known, in Bays–Ford–Hudson–Rubinstein (low zero 0.2029, Chowla–Selberg explanation, prime race mod 163 skewed below 10¹⁰), so a rediscovery. Claude corrected the summary: the drift comes from one slow wave, the lowest zero, whose amplitude is the largest, not from many small effects accumulating. |
| 57 | Zeta | Update the paper before deciding the next step. | Version 11 adds §16, "Impurities, extreme values and slow waves" (entries 50–56). The BFHR reference was verified as J. Number Theory 87 (2001), 54–76. |
| 58 | ChatGPT | Review of Part IV (issue #2): the torus is an obstruction, not an approximate Stepanov mechanism; the explanation of critical-line non-convergence via the pole; orthogonality is always exact, so only the diagonal reduction is restricted; the amplifier result is ex post; extreme values are a heuristic, with all eight moduli to be shown; define apparent impurity; present the quasi-RH link as an analogy. | Adopted in v12, the §14 point in part: the outward winding *is* the pole's main term x^{1−s}/((1−s) log x), but the pole is no longer given as the general reason for non-convergence (Conrad 2005 cited). All Part IV scripts were rerun and the outputs are identical. |
