# Step 4(a): what a theta lift does to the Frobenius data — a literature check

*Written by Claude (Anthropic, Claude Opus 5.5) at the request of Zeta Hoi-Ho Cheng, 22 November 2026.*

Step 3 ended at the crux (C): the verified proof needs multiplicity at a cost **linear** in the chain length m, while naive iteration over ℤ (raising to the p-th power) costs exponentially. In step 4 we try to see how iterated theta lifts get around this. Part (a) checks against published sources the classical fact our reading rests on: at an unramified place, a theta lift **appends a block** of Frobenius eigenvalues to those of the original form.

## Provenance tiers

| tier | source | what it says |
|---|---|---|
| classical theorem | Rallis (1982), stated in Kudla, *Notes on the local theta correspondence*, §VI.4; Theorem 8.1 of arXiv 2303.14919 | orthogonal–symplectic pairs, unramified: the Satake parameter of θ(π) is that of π **plus a fixed block** |
| conjecture (Adams), partly proved | Harris–Kudla–Sweet, JAMS 9 (1996), Conjecture 7.2, eq. (0.13), (7.38); Conjecture 8.2 of 2303.14919 | same shape for unitary pairs: parameter of θ(π) = (parameter of π)·μ₁ ⊕ μ₂·S_b |
| not read by us | Rallis 1982; Liu 2011, Appendix (cited by Liu, arXiv 2105.14223, Remark 1.4) | the unramified statement for **unitary** pairs |
| secondary, AI-assisted, unverified | R. Zhang, preliminary note on Alpöge's proof, 20 Nov 2026 | the chain of lifts used in the proof, and the Galois data ξ_c = ξ₁ε^{−(c−1)ℓ}, 1 ≤ c ≤ h |
| our reading | this note | that the divisibility in the proof comes from these appended blocks |

## 1. The classical fact (orthogonal–symplectic case, a theorem)

Let dim W = 2n and dim V = 2m > 2n. At an unramified place with residue field of size q, unramified representations correspond to unramified representations (Howe). By Rallis, the Satake parameter s of σ on Sp(W) goes to

  s ⊕ Sym^{2m−2n−2}(q^{1/2}, q^{−1/2}) ∈ SO_{2n+1}(ℂ) × SO_{2m−2n−1}(ℂ) ⊂ O_{2m}(ℂ)

(2303.14919, Thm 8.1; Kudla §VI.4 states this through an explicit L-homomorphism C). The appended block has eigenvalues

  q^{m−n−1}, q^{m−n−2}, …, q^{−(m−n−1)},

which are **powers of q**, independent of σ, and their number is (dimension of the larger group) minus (dimension of the smaller one). Adams' conjecture is the same statement for Arthur parameters: Ψ ↦ Ψ ⊕ S_{dim V − dim W − 1}.

## 2. The unitary case (the case the proof uses)

For U(V) × U(W) with splitting characters χ = (χ₁, χ₂), Adams' conjecture in the form of Harris–Kudla–Sweet (Conj. 7.2) has the parameter map built from μ₁ = χ₁^{−1}χ₂ and μ₂ = χ₂ with a tail ρ_b. Along a chain of lifts the parameters grow by successive blocks, φ_r = φ₀ ⊕ χ(ρ₂ ⊕ ρ₄ ⊕ ⋯ ⊕ ρ_{2r}) (eq. (0.13), conjectural for supercuspidal chains). The local factor of one block is

  L(s, χ^{−1}ρ_b, χ) = (1 − q_E^{−(s+(b−1)/2)})^{−1}  (eq. (7.38)),

the signature of a block of Tate twists. At an **inert** prime p of E/E⁺, q_E = p². For unramified data this is, to our knowledge, a theorem (Rallis; Liu 2011, Appendix), but we have not read that statement ourselves. We record it as **not checked by us**.

## 3. Comparison with Zhang's description of the proof

Zhang's note gives the Galois data at the retained eigensystems as ξ_c = ξ₁ ε^{−(c−1)ℓ} for 1 ≤ c ≤ h, where ε is the cyclotomic character. Frobenius at p acts on ε^{−(c−1)ℓ} by p^{−(c−1)ℓ}, so this is a block of h Tate twists, which has the shape of §1–2. (The spacing ℓ instead of 1 presumably reflects the weights chosen in the proof; we cannot check this.)

## 4. Dimension bookkeeping (computed by us from Zhang's formulas)

Zhang gives dim X_j = k + j(h+1) and dim Y_j = r + jh with r = k + m − 1 and h ≥ r + 5. Then:

| lift | dimension added |
|---|---|
| X_j → Y_j | m − 1 − j (≥ 0 for j ≤ m − 1) |
| Y_j → X_{j+1} | h + 2 + j − m (≥ k + j + 6) |
| one round, X_j → X_{j+1} | **h + 1, independent of j** |

Both steps go upward, so each appends a block. The two block lengths change with j, but their sum does not.

## What (a) establishes, and what it does not

**Established (theorem, orthogonal–symplectic; conjecture with partial results, unitary):** a theta lift acts on unramified Frobenius data by **direct sum** with a block of powers of q whose length is fixed by the dimensions alone. Iterating m times appends m blocks. Dimension, and therefore degree in the sense of step 3, grows **additively**: h + 1 per round in the proof's chain.

In the picture of the paper: Frobenius, "turning the circle n times", acts on eigenvalues by α ↦ α^n, which is multiplicative and is the source of the exponential cost in step 3 (C). A theta lift does not turn the existing points. It **adds a fixed segment of new points at radii p^c**, which is additive.

**Not established:**
1. That these blocks produce **divisibility** of the normalised periods. Eigenvalues that are powers of p suggest p-adic valuation, but the period values are a separate object. Zhang's note states the resulting valuation inequality and does not show the local computation.
2. That the **archimedean size** stays controlled. The block eigenvalues q^{±c} have archimedean size as large as their p-adic smallness, so by the product formula a block alone gives no net gain. The gain must come from the normalisation of the periods (Zhang, Lemma 4.2: the normalised operators are close to isometries). That is part (c), and a toy computation cannot settle it.
3. The exact unitary unramified statement, which we have not read.

Next, (b): a toy comparison of "append m blocks" against "iterate Frobenius m times", measuring p-adic valuation and size, with point 2 kept explicitly in view so that the toy does not appear to prove more than it does.

## Sources

- S. Kudla, *Notes on the local theta correspondence*, §VI.4 — https://www.math.utoronto.ca/~skudla/castle.pdf
- *Explicit constructions of automorphic forms: theta correspondence and automorphic descent*, arXiv 2303.14919, Thm 8.1, Conj. 8.2
- M. Harris, S. Kudla, W. J. Sweet, *Theta dichotomy for unitary groups*, JAMS 9 (1996)
- Y. Liu, *Theta correspondence for almost unramified representations of unitary groups*, arXiv 2105.14223 (Remark 1.4, citing Rallis 1982 and Liu 2011)
- R. Zhang, *A preliminary note on Alpöge's proposed proof of the GRH* (20 Nov 2026) — https://www.ihes.fr/~rzhang/files/GRH%20note.pdf
