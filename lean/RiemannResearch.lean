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

namespace RiemannResearch

/-- v16, q = 1: the real Chebyshev function using von Mangoldt weights. -/
noncomputable def chebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nat.floor x + 1), ArithmeticFunction.vonMangoldt n

noncomputable def primeError (x : ℝ) : ℝ := x - chebyshevPsi x

def OneSidedBound (theta : ℝ) : Prop :=
  ∃ C x0 : ℝ, 0 ≤ C ∧ 1 ≤ x0 ∧
    ∀ x : ℝ, x0 ≤ x → primeError x ≤ C * x ^ theta

/-- The nonnegative tail required by Landau's argument. -/
theorem tail_nonneg (theta : ℝ) (h : OneSidedBound theta) :
    ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      0 ≤ C * x ^ theta - primeError x := by
  obtain ⟨C, x0, _, _, h⟩ := h
  exact ⟨C, x0, fun x hx => sub_nonneg.mpr (h x hx)⟩

/-- Step (iv): a negative pole cannot coexist with a nonnegative tail
and a bounded initial contribution. This is the algebraic part only. -/
theorem negative_pole_contradiction (m beta d B R F0 F1 : ℝ)
    (hm : 0 < m) (hb : 0 < beta) (hd : 0 < d)
    (hsmall : beta * d * (B + B + 1) < m)
    (hB : 0 ≤ B) (hR : R ≤ -(m / (beta * d)) + B)
    (hF0 : -B ≤ F0) (hF1 : 0 ≤ F1)
    (heq : R = F0 + F1) : False := by
  have hp : 0 < beta * d := mul_pos hb hd
  have hlarge : B + B + 1 < m / (beta * d) := by
    apply (lt_div_iff₀ hp).2
    simpa [mul_comm] using hsmall
  linarith

/-- Abstract final reduction: a zero set symmetric under real-part
reflection and free of zeros to the right of every theta in (1/2,1)
lies on the critical line. No zeta-specific analytic fact is assumed proved. -/
theorem critical_line_of_zero_free (Z : Set ℂ)
    (hreflect : ∀ z ∈ Z, 1 - z ∈ Z)
    (hfree : ∀ theta : ℝ, 1/2 < theta → theta < 1 →
      ∀ z ∈ Z, z.re ≤ theta) :
    ∀ z ∈ Z, z.re = 1/2 := by
  have upper : ∀ z ∈ Z, z.re ≤ 1/2 := by
    intro z hz
    by_contra! h
    let theta : ℝ := min ((z.re + 1/2) / 2) (3/4)
    have ht : 1/2 < theta := lt_min (by linarith) (by norm_num)
    have ht1 : theta < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hzle := hfree theta ht ht1 z hz
    have hmid : theta ≤ (z.re + 1/2) / 2 := min_le_left _ _
    linarith
  intro z hz
  have hu := upper z hz
  have hl := upper (1 - z) (hreflect z hz)
  simp at hl
  linarith

#print axioms tail_nonneg
#print axioms negative_pole_contradiction
#print axioms critical_line_of_zero_free

end RiemannResearch
