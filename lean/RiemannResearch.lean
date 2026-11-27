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
    (hb : 0 < beta) (hd : 0 < d)
    (hsmall : beta * d * (B + B + 1) < m)
    (hR : R ≤ -(m / (beta * d)) + B)
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

namespace RiemannResearch

open MeasureTheory

/-- Real Mellin tail, after x = exp t. The integral is a totalized
Lebesgue integral; convergence is a separate obligation. -/
noncomputable def mellinTail (g : ℝ → ℝ) (a s : ℝ) : ℝ :=
  ∫ t in Set.Ici a, g (Real.exp t) * Real.exp (-s * t)

/-- Positivity of the actual real Mellin integral. -/
theorem mellinTail_nonneg (g : ℝ → ℝ) (a s : ℝ)
    (hg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t)) :
    0 ≤ mellinTail g a s := by
  unfold mellinTail
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact mul_nonneg (hg t ht) (Real.exp_pos _).le

/-- The exponential kernel decreases as the real Mellin parameter grows. -/
theorem mellin_kernel_le (t s u : ℝ) (ht : 0 ≤ t) (hs : s ≤ u) :
    Real.exp (-u * t) ≤ Real.exp (-s * t) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hs) ht

/-- Nonnegative Taylor moments, the input to Landau's Taylor argument. -/
theorem mellin_moment_nonneg (g : ℝ → ℝ) (a s : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t)) :
    0 ≤ ∫ t in Set.Ici a, g (Real.exp t) * Real.exp (-s * t) * t ^ k := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact mul_nonneg (mul_nonneg (hg t ht) (Real.exp_pos _).le)
    (pow_nonneg (le_trans ha ht) _)

/-- Finite Taylor lower bound for exp on the positive axis, expressed
as a recurrence. This does not assert convergence of the infinite series. -/
theorem landau_partial_sum_nonneg (c : ℕ → ℝ) (r : ℝ) (N : ℕ)
    (hc : ∀ k, 0 ≤ c k) (hr : 0 ≤ r) :
    0 ≤ ∑ k ∈ Finset.range N, c k * r ^ k := by
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hc k) (pow_nonneg hr _))

/-- Abstract abscissa contradiction: a convergence point strictly to
the left of a lower bound on all convergence points is impossible.
The Taylor/monotone-convergence argument producing that point is open. -/
theorem landau_abscissa_contradiction (converges : ℝ → Prop)
    (sigma r : ℝ) (hr : 0 < r)
    (hlower : ∀ s, converges s → sigma ≤ s)
    (hleft : converges (sigma - r)) : False := by
  have h := hlower (sigma - r) hleft
  linarith

#print axioms mellinTail_nonneg
#print axioms mellin_kernel_le
#print axioms mellin_moment_nonneg
#print axioms landau_partial_sum_nonneg
#print axioms landau_abscissa_contradiction

end RiemannResearch

namespace RiemannResearch
open MeasureTheory

/-- Actual absolute convergence propagates to the right, by domination. -/
theorem mellin_integrable_right (g : ℝ → ℝ) (a s u : ℝ)
    (ha : 0 ≤ a) (hs : s ≤ u)
    (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a))) :
    Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-u * t))
      (volume.restrict (Set.Ici a)) := by
  apply hi.mono ((hg.comp Real.continuous_exp.measurable).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  change ‖g (Real.exp t) * Real.exp (-u * t)‖ ≤ ‖g (Real.exp t) * Real.exp (-s * t)‖
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (mellin_kernel_le t s u (le_trans ha ht) hs) (abs_nonneg _)

/-- Nonnegative integration commutes with countable summation.
This is the Tonelli step in Landau's proof, not the analytic continuation step. -/
theorem landau_tonelli (f : ℕ → ℝ → ENNReal) (a : ℝ)
    (hf : ∀ n, Measurable (f n)) :
    (∫⁻ t in Set.Ici a, ∑' n, f n t) =
      ∑' n, ∫⁻ t in Set.Ici a, f n t := by
  exact lintegral_tsum (fun n => (hf n).aemeasurable)

/-- If the pointwise Taylor sum is the shifted integrand and its
integrated coefficients have finite sum, the shifted integral is finite.
The pointwise exponential expansion and coefficient identification
are explicit hypotheses, not new axioms. -/
theorem landau_shift_finite (f : ℕ → ℝ → ENNReal)
    (G : ℝ → ENNReal) (a : ℝ)
    (hf : ∀ n, Measurable (f n))
    (hseries : ∀ t, G t = ∑' n, f n t)
    (hfinite : (∑' n, ∫⁻ t in Set.Ici a, f n t) < ⊤) :
    (∫⁻ t in Set.Ici a, G t) < ⊤ := by
  have heq : G = fun t => ∑' n, f n t := funext hseries
  rw [heq, landau_tonelli f a hf]
  exact hfinite

#print axioms mellin_integrable_right
#print axioms landau_tonelli
#print axioms landau_shift_finite
end RiemannResearch

namespace RiemannResearch
open MeasureTheory

/-- Polynomial moments are integrable at s whenever the original
integrand is integrable at a smaller parameter and the polynomial
is dominated by the intervening exponential. -/
theorem mellin_moment_integrable (g : ℝ → ℝ) (a s u : ℝ) (k : ℕ)
    (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hdom : ∀ t : ℝ, a ≤ t →
      |t ^ k| * Real.exp (-u * t) ≤ Real.exp (-s * t)) :
    Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-u * t) * t ^ k)
      (volume.restrict (Set.Ici a)) := by
  apply hi.mono (((hg.comp Real.continuous_exp.measurable).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul
    (continuous_id.pow k).measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  change ‖g (Real.exp t) * Real.exp (-u * t) * t ^ k‖ ≤
    ‖g (Real.exp t) * Real.exp (-s * t)‖
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |g (Real.exp t)| * Real.exp (-u * t) * |t ^ k| =
        |g (Real.exp t)| * (|t ^ k| * Real.exp (-u * t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hdom t ht) (abs_nonneg _)

/-- Exponential domination of each polynomial moment, with an explicit
factorial constant. This is the quantitative bound needed for
differentiation under the integral. -/
theorem mellin_polynomial_bound (t d : ℝ) (k : ℕ)
    (hd : 0 < d)
    (hexp : (d * t) ^ k / (k.factorial : ℝ) ≤ Real.exp (d * t)) :
    t ^ k ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * t) := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hp : 0 < d ^ k := pow_pos hd _
  have h := (div_le_iff₀ hf).mp hexp
  rw [mul_pow] at h
  calc
    t ^ k ≤ Real.exp (d * t) * (k.factorial : ℝ) / d ^ k := by
      apply (le_div_iff₀ hp).2
      simpa [mul_comm] using h
    _ = _ := by ring

/-- Mellin transform of a single exponential on a finite interval,
via the fundamental theorem of calculus. -/
theorem mellin_exp_interval (s a b : ℝ) (hs : s ≠ 0) :
    (∫ t in a..b, Real.exp (-s * t)) =
      Real.exp (-s * b) / (-s) - Real.exp (-s * a) / (-s) := by
  have hn : -s ≠ 0 := neg_ne_zero.mpr hs
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have h := ((hasDerivAt_id t).const_mul (-s)).exp.div_const (-s)
    convert h using 1
    field_simp [hn]
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b

#print axioms mellin_moment_integrable
#print axioms mellin_polynomial_bound
#print axioms mellin_exp_interval
end RiemannResearch

namespace RiemannResearch
open MeasureTheory

/-- Unconditional polynomial domination on the nonnegative axis. -/
theorem mellin_polynomial_bound_pos (t d : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hd : 0 < d) :
    t ^ k ≤ ((k.factorial : ℝ) / d ^ k) * Real.exp (d * t) := by
  apply mellin_polynomial_bound t d k hd
  exact Real.pow_div_factorial_le_exp (mul_nonneg hd.le ht) k

/-- All polynomial moments are integrable strictly inside the real
half-line of absolute convergence. -/
theorem mellin_moments_inside (g : ℝ → ℝ) (a s u : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hs : s < u) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a))) :
    Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-u * t) * t ^ k)
      (volume.restrict (Set.Ici a)) := by
  let C : ℝ := (k.factorial : ℝ) / (u - s) ^ k
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply (hi.const_mul C).mono
    (((hg.comp Real.continuous_exp.measurable).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul
    (continuous_id.pow k).measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  have ht0 : 0 ≤ t := le_trans ha ht
  have hp := mellin_polynomial_bound_pos t (u - s) k ht0 (sub_pos.mpr hs)
  change t ^ k ≤ C * Real.exp ((u - s) * t) at hp
  change ‖g (Real.exp t) * Real.exp (-u * t) * t ^ k‖ ≤
    ‖C * (g (Real.exp t) * Real.exp (-s * t))‖
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hC, abs_of_nonneg (pow_nonneg ht0 k)]
  calc
    |g (Real.exp t)| * Real.exp (-u * t) * t ^ k ≤
        |g (Real.exp t)| * Real.exp (-u * t) *
          (C * Real.exp ((u - s) * t)) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    _ = C * (|g (Real.exp t)| * Real.exp (-s * t)) := by
      rw [show (u - s) * t = u * t - s * t by ring, Real.exp_sub]
      rw [show -u * t = -(u * t) by ring, Real.exp_neg]
      field_simp [ne_of_gt (Real.exp_pos (u * t))]
      <;> ring

/-- Complex exponential Mellin kernel on finite real intervals. -/
theorem mellin_complex_exp_interval (s : ℂ) (a b : ℝ) (hs : s ≠ 0) :
    (∫ t in a..b, Complex.exp (-s * (t : ℂ))) =
      Complex.exp (-s * (b : ℂ)) / (-s) -
      Complex.exp (-s * (a : ℂ)) / (-s) := by
  have hn : -s ≠ 0 := neg_ne_zero.mpr hs
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have h := ((Complex.ofRealCLM.hasDerivAt).const_mul (-s)).cexp.div_const (-s)
    convert h using 1 <;> simp [hn]
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable a b

#print axioms mellin_polynomial_bound_pos
#print axioms mellin_moments_inside
#print axioms mellin_complex_exp_interval
end RiemannResearch
