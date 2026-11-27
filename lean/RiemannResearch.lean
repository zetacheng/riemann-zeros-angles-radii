import Mathlib

namespace RiemannResearch

/-- Finite auxiliary radial energy, with arbitrary real frequencies. -/
noncomputable def radialEnergy (w L : ℕ → ℝ) (N : ℕ) (a : ℝ) : ℝ :=
  4 * ∑ k ∈ Finset.range N, w k * (Real.sinh (a * L k)) ^ 2

theorem radialEnergy_nonneg (w L : ℕ → ℝ) (N : ℕ) (a : ℝ)
    (hw : ∀ k, 0 ≤ w k) : 0 ≤ radialEnergy w L N a := by
  unfold radialEnergy
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (sq_nonneg _))

theorem radialEnergy_zero (w L : ℕ → ℝ) (N : ℕ) :
    radialEnergy w L N 0 = 0 := by
  simp [radialEnergy]

/-- Algebraic paired-channel cancellation; not a statement about zeta zeros. -/
theorem paired_variance (v : ℝ) : v + v - 2 * v = 0 := by ring

#print axioms radialEnergy_nonneg
#print axioms radialEnergy_zero
#print axioms paired_variance
#check RiemannHypothesis

end RiemannResearch
