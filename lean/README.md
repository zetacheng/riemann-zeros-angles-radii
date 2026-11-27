# Formalization pilot

Pinned Lean and Mathlib v4.19.0. Run `lake update`, `lake exe cache get`, then `lake build` from this directory. Initial source is unverified until CI succeeds. No RH proof is claimed.

The pilot formalizes finite auxiliary radial-energy nonnegativity and its zero at the origin, plus the scalar cancellation identity. These do not distinguish RH true from false. Next: formalize the one-sided prime-error criterion and identify the exact missing arithmetic estimate. Keep conjectures outside the verified library; no sorry or new axioms. The final target is Mathlib's RiemannHypothesis, not a replacement definition.
