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
  apply Real.pow_div_factorial_le_exp
  exact mul_nonneg hd.le ht

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
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hs.le) _)
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
      have he : Real.exp (-u * t) * Real.exp ((u - s) * t) = Real.exp (-s * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = C * (|g (Real.exp t)| * (Real.exp (-u * t) * Real.exp ((u - s) * t))) := by ring
        _ = _ := by rw [he]

/-- Complex exponential Mellin kernel on finite real intervals. -/
theorem mellin_complex_exp_interval (s : ℂ) (a b : ℝ) (hs : s ≠ 0) :
    (∫ t in a..b, Complex.exp (-s * (t : ℂ))) =
      Complex.exp (-s * (b : ℂ)) / (-s) -
      Complex.exp (-s * (a : ℂ)) / (-s) := by
  have hn : -s ≠ 0 := neg_ne_zero.mpr hs
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp.div_const (-s)
    convert h using 1 <;> simp [hn, hs]
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable a b

#print axioms mellin_polynomial_bound_pos
#print axioms mellin_moments_inside
#print axioms mellin_complex_exp_interval
end RiemannResearch

namespace RiemannResearch
open MeasureTheory

/-- Pointwise derivative of the real Mellin moment kernel. -/
theorem mellin_moment_kernel_deriv (g : ℝ → ℝ) (t s : ℝ) (k : ℕ) :
    HasDerivAt (fun u : ℝ => g (Real.exp t) * Real.exp (-u * t) * t ^ k)
      (-(g (Real.exp t) * Real.exp (-s * t) * t ^ (k+1))) s := by
  have h := (((hasDerivAt_id s).neg.mul_const t).exp.const_mul
    (g (Real.exp t))).mul_const (t ^ k)
  convert h using 1 <;> simp [pow_succ] <;> ring

/-- Exact absolute value of the complex exponential kernel. -/
theorem mellin_complex_kernel_norm (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * (t : ℂ))‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The complex kernel is absolutely integrable whenever its real
majorant is integrable on the tail. -/
theorem mellin_complex_integrable (s : ℂ) (a : ℝ)
    (hi : Integrable (fun t : ℝ => Real.exp (-s.re * t))
      (volume.restrict (Set.Ici a))) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
      (volume.restrict (Set.Ici a)) := by
  apply hi.mono (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  filter_upwards [] with t
  change ‖Complex.exp (-s * (t : ℂ))‖ ≤ ‖Real.exp (-s.re * t)‖
  rw [mellin_complex_kernel_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

#print axioms mellin_moment_kernel_deriv
#print axioms mellin_complex_kernel_norm
#print axioms mellin_complex_integrable
end RiemannResearch

namespace RiemannResearch
open MeasureTheory

/-- Uniform integrable derivative majorant on the parameter half-line
v ≤ u, with v strictly inside the convergence region. -/
theorem mellin_derivative_majorant (g : ℝ → ℝ) (a s v : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hsv : s < v) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a))) :
    ∃ M : ℝ → ℝ, Integrable M (volume.restrict (Set.Ici a)) ∧
      ∀ t u : ℝ, a ≤ t → v ≤ u →
        ‖-(g (Real.exp t) * Real.exp (-u * t) * t ^ (k+1))‖ ≤ M t := by
  let M : ℝ → ℝ := fun t => ‖g (Real.exp t) * Real.exp (-v * t) * t ^ (k+1)‖
  refine ⟨M, (mellin_moments_inside g a s v (k+1) ha hsv hg hi).norm, ?_⟩
  intro t u ht hu
  have ht0 : 0 ≤ t := le_trans ha ht
  dsimp [M]
  simp only [norm_neg, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mellin_kernel_le t v u ht0 hu) (abs_nonneg _))
    (abs_nonneg _)

/-- The complex kernel tends to zero at positive infinity in its
right half-plane. -/
theorem mellin_complex_kernel_decay (s : ℂ) (hs : 0 < s.re) :
    Filter.Tendsto (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [mellin_complex_kernel_norm]
  have h : Filter.Tendsto (fun t : ℝ => -s.re * t) Filter.atTop Filter.atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hs) Filter.tendsto_id
  exact Real.tendsto_exp_atBot.comp h

#print axioms mellin_derivative_majorant
#print axioms mellin_complex_kernel_decay
end RiemannResearch

namespace RiemannResearch
open MeasureTheory Filter

/-- Evaluation of the improper complex exponential integral as a
limit of finite interval integrals. -/
theorem mellin_complex_improper_limit (s : ℂ) (a : ℝ) (hs : 0 < s.re) :
    Tendsto (fun b : ℝ => ∫ t in a..b, Complex.exp (-s * (t : ℂ)))
      atTop (nhds (Complex.exp (-s * (a : ℂ)) / s)) := by
  have hn : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (lt_irrefl 0) hs
  have h := ((mellin_complex_kernel_decay s hs).div_const (-s)).sub
    (tendsto_const_nhds (x := Complex.exp (-s * (a : ℂ)) / (-s)))
  simpa only [mellin_complex_exp_interval s a _ hn, zero_div, zero_sub,
    div_neg, neg_zero, zero_sub, neg_neg] using h

set_option maxHeartbeats 2000000 in
/-- First derivative of the integrated real moment, via the dominated
differentiation theorem. -/
theorem mellin_integral_moment_deriv (g : ℝ → ℝ) (a s u : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hs : s < u) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a))) :
    HasDerivAt
      (fun z : ℝ => ∫ t in Set.Ici a, g (Real.exp t) * Real.exp (-z * t) * t ^ k)
      (∫ t in Set.Ici a, -(g (Real.exp t) * Real.exp (-u * t) * t ^ (k+1))) u := by
  let v := (s + u) / 2
  have hsv : s < v := by dsimp [v]; linarith
  have hvu : v < u := by dsimp [v]; linarith
  obtain ⟨M, hM, hbound⟩ := mellin_derivative_majorant g a s v k ha hsv hg hi
  have hmeas : ∀ z : ℝ, AEStronglyMeasurable
      (fun t : ℝ => g (Real.exp t) * Real.exp (-z * t) * t ^ k)
      (volume.restrict (Set.Ici a)) := fun z =>
    (((hg.comp Real.continuous_exp.measurable).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable).mul
      (continuous_id.pow k).measurable).aestronglyMeasurable
  have hderivmeas : AEStronglyMeasurable
      (fun t : ℝ => -(g (Real.exp t) * Real.exp (-u * t) * t ^ (k+1)))
      (volume.restrict (Set.Ici a)) :=
    (mellin_moments_inside g a s u (k+1) ha hs hg hi).neg.aestronglyMeasurable
  have hdom : ∀ᵐ t ∂(volume.restrict (Set.Ici a)), ∀ z ∈ Set.Ioi v,
      ‖-(g (Real.exp t) * Real.exp (-z * t) * t ^ (k+1))‖ ≤ M t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht z hz
    exact hbound t z ht (le_of_lt hz)
  have hd : ∀ᵐ t ∂(volume.restrict (Set.Ici a)), ∀ z ∈ Set.Ioi v,
      HasDerivAt (fun w : ℝ => g (Real.exp t) * Real.exp (-w * t) * t ^ k)
        (-(g (Real.exp t) * Real.exp (-z * t) * t ^ (k+1))) z :=
    Filter.Eventually.of_forall (fun t z _ => mellin_moment_kernel_deriv g t z k)
  have he : 0 < u - v := sub_pos.mpr hvu
  have hball : ∀ z ∈ Metric.ball u (u - v), z ∈ Set.Ioi v := by
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq] at hz
    have hl := (abs_lt.mp hz).1
    change v < z
    linarith
  have hb : ∀ᵐ t ∂(volume.restrict (Set.Ici a)), ∀ z ∈ Metric.ball u (u-v),
      ‖-(g (Real.exp t) * Real.exp (-z * t) * t ^ (k+1))‖ ≤ M t :=
    hdom.mono (fun t ht z hz => ht z (hball z hz))
  have hdb : ∀ᵐ t ∂(volume.restrict (Set.Ici a)), ∀ z ∈ Metric.ball u (u-v),
      HasDerivAt (fun w : ℝ => g (Real.exp t) * Real.exp (-w * t) * t ^ k)
        (-(g (Real.exp t) * Real.exp (-z * t) * t ^ (k+1))) z :=
    hd.mono (fun t ht z hz => ht z (hball z hz))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le he
    (Filter.Eventually.of_forall hmeas)
    (mellin_moments_inside g a s u k ha hs hg hi)
    hderivmeas hb hM hdb).2

#print axioms mellin_complex_improper_limit
#print axioms mellin_integral_moment_deriv

/-- Inside the domain of convergence, every real derivative of the Mellin tail
is the corresponding integral moment with its alternating sign. -/
theorem mellinTail_iteratedDeriv (g : ℝ → ℝ) (a s : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a))) :
    ∀ u > s, iteratedDeriv k (mellinTail g a) u =
      (-1 : ℝ) ^ k * ∫ t in Set.Ici a, g (Real.exp t) * Real.exp (-u * t) * t ^ k := by
  induction k with
  | zero =>
    intro u _
    simp [mellinTail]
  | succ k ih =>
    intro u hu
    have hlocal : iteratedDeriv k (mellinTail g a) =ᶠ[nhds u]
        (fun z : ℝ => (-1 : ℝ) ^ k *
          ∫ t in Set.Ici a, g (Real.exp t) * Real.exp (-z * t) * t ^ k) := by
      filter_upwards [Ioi_mem_nhds hu] with z hz
      exact ih z hz
    have hnext := (mellin_integral_moment_deriv g a s u k ha hu hg hi).const_mul
      ((-1 : ℝ) ^ k)
    rw [iteratedDeriv_succ, hlocal.deriv_eq, hnext.deriv, integral_neg, pow_succ]
    ring

/-- The Taylor coefficients for a leftward shift are nonnegative when the
Mellin tail has a nonnegative integrand. -/
theorem mellinTail_left_taylor_coeff_nonneg (g : ℝ → ℝ) (a s u : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hu : s < u) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hnonneg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t)) :
    0 ≤ ((-1 : ℝ) ^ k * iteratedDeriv k (mellinTail g a) u) / (k.factorial : ℝ) := by
  rw [mellinTail_iteratedDeriv g a s k ha hg hi u hu, ← mul_assoc]
  exact div_nonneg (mul_nonneg (by rw [← mul_pow]; norm_num)
    (mellin_moment_nonneg g a u k ha hnonneg)) (Nat.cast_nonneg _)

#print axioms mellinTail_iteratedDeriv
#print axioms mellinTail_left_taylor_coeff_nonneg

/-- A convergent leftward Taylor series of a nonnegative Mellin tail
gives absolute convergence at the shifted parameter, with the same sum. -/
theorem mellinTail_left_taylor_integrable (g : ℝ → ℝ) (a s u r L : ℝ)
    (ha : 0 ≤ a) (hu : s < u) (hr : 0 ≤ r) (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hnonneg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t))
    (hsum : HasSum (fun n : ℕ =>
      ((-1 : ℝ) ^ n * iteratedDeriv n (mellinTail g a) u) / (n.factorial : ℝ) * r ^ n) L) :
    Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-(u - r) * t))
        (volume.restrict (Set.Ici a)) ∧
      mellinTail g a (u - r) = L := by
  let μ := volume.restrict (Set.Ici a)
  let kernel (v : ℝ) (t : ℝ) := g (Real.exp t) * Real.exp (-v * t)
  let weight (n : ℕ) : ℝ := r ^ n / n.factorial
  let term (n : ℕ) (t : ℝ) := kernel u t * t ^ n * weight n
  have hkernel_meas (v : ℝ) : Measurable (kernel v) :=
    (hg.comp Real.continuous_exp.measurable).mul (by fun_prop)
  have hkernel_nonneg (v t : ℝ) (ht : a ≤ t) : 0 ≤ kernel v t :=
    mul_nonneg (hnonneg t ht) (Real.exp_pos _).le
  have hterm_nonneg (n : ℕ) (t : ℝ) (ht : a ≤ t) : 0 ≤ term n t :=
    mul_nonneg (mul_nonneg (hkernel_nonneg u t ht) (pow_nonneg (ha.trans ht) n))
      (div_nonneg (pow_nonneg hr n) (Nat.cast_nonneg _))
  have hterm_meas (n : ℕ) : Measurable (term n) :=
    ((hkernel_meas u).mul (measurable_id.pow_const n)).mul_const (weight n)
  have hterm_int (n : ℕ) : Integrable (term n) μ :=
    (mellin_moments_inside g a s u n ha hu hg hi).mul_const (weight n)
  have hcoeff (n : ℕ) : (∫ t, term n t ∂μ) =
      ((-1 : ℝ) ^ n * iteratedDeriv n (mellinTail g a) u) / (n.factorial : ℝ) * r ^ n := by
    have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    dsimp only [term, weight, kernel, μ]
    rw [integral_mul_const, mellinTail_iteratedDeriv g a s n ha hg hi u hu,
      ← mul_assoc, hsign, one_mul]
    simp only [div_eq_mul_inv]
    ring
  have hpoint (t : ℝ) : HasSum (fun n => term n t) (kernel (u - r) t) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp ℝ (r * t)).mul_left (kernel u t)
    rw [← Real.exp_eq_exp_ℝ] at h
    have heq : kernel u t * Real.exp (r * t) = kernel (u - r) t := by
      dsimp [kernel]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq] at h
    simpa only [term, weight, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hmem : ∀ᵐ t ∂μ, t ∈ Set.Ici a := ae_restrict_mem measurableSet_Ici
  have hint_nonneg (n : ℕ) : 0 ≤ ∫ t, term n t ∂μ :=
    integral_nonneg_of_ae (hmem.mono fun t ht => hterm_nonneg n t ht)
  have hcoef_sum : HasSum (fun n => ∫ t, term n t ∂μ) L := by
    simpa only [hcoeff] using hsum
  have hlin : (∫⁻ t, ENNReal.ofReal (kernel (u - r) t) ∂μ) = ENNReal.ofReal L := by
    calc
      _ = ∫⁻ t, ∑' n, ENNReal.ofReal (term n t) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hmem] with t ht
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hterm_nonneg n t ht)
          (hpoint t).summable, (hpoint t).tsum_eq]
      _ = ∑' n, ∫⁻ t, ENNReal.ofReal (term n t) ∂μ :=
        landau_tonelli (fun n t => ENNReal.ofReal (term n t)) a
          (fun n => (hterm_meas n).ennreal_ofReal)
      _ = ENNReal.ofReal L := by
        simp_rw [← ofReal_integral_eq_lintegral_ofReal (hterm_int _)
          (hmem.mono fun t ht => hterm_nonneg _ t ht)]
        rw [← ENNReal.ofReal_tsum_of_nonneg hint_nonneg hcoef_sum.summable, hcoef_sum.tsum_eq]
  have hnonneg_ae : 0 ≤ᵐ[μ] kernel (u - r) :=
    hmem.mono fun t ht => hkernel_nonneg (u - r) t ht
  have hshift : Integrable (kernel (u - r)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hkernel_meas (u - r)).aestronglyMeasurable hnonneg_ae).mp
      (hlin.trans_ne ENNReal.ofReal_ne_top)
  have hL : 0 ≤ L := hcoef_sum.tsum_eq ▸ tsum_nonneg hint_nonneg
  refine ⟨hshift, ?_⟩
  change (∫ t, kernel (u - r) t ∂μ) = L
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg_ae hshift.aestronglyMeasurable,
    hlin, ENNReal.toReal_ofReal hL]

/-- A leftward Taylor series cannot converge at a point below a lower bound
for absolute convergence of the original Mellin integral. -/
theorem mellinTail_left_taylor_not_summable (g : ℝ → ℝ) (a s u r σ : ℝ)
    (ha : 0 ≤ a) (hu : s < u) (hr : 0 ≤ r) (hleft : u - r < σ)
    (hg : Measurable g)
    (hi : Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hnonneg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t))
    (hlower : ∀ v : ℝ, Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-v * t))
      (volume.restrict (Set.Ici a)) → σ ≤ v) :
    ¬ Summable (fun n : ℕ =>
      ((-1 : ℝ) ^ n * iteratedDeriv n (mellinTail g a) u) / (n.factorial : ℝ) * r ^ n) := by
  intro hsum
  exact not_le_of_gt hleft (hlower _ (mellinTail_left_taylor_integrable g a s u r _
    ha hu hr hg hi hnonneg hsum.hasSum).1)

#print axioms mellinTail_left_taylor_integrable
#print axioms mellinTail_left_taylor_not_summable

/-- A nonnegative Mellin tail has no real-analytic continuation through
its finite abscissa of absolute convergence. -/
theorem mellinTail_not_analyticAt_abscissa (g : ℝ → ℝ) (a σ : ℝ)
    (ha : 0 ≤ a) (hg : Measurable g)
    (hnonneg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t))
    (hupper : ∀ s > σ, Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hlower : ∀ s : ℝ, Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)) → σ ≤ s) :
    ¬ ∃ F : ℝ → ℝ, AnalyticAt ℝ F σ ∧ F =ᶠ[nhdsWithin σ (Set.Ioi σ)] mellinTail g a := by
  rintro ⟨F, ⟨p, R, hp⟩, hagree⟩
  obtain ⟨δ, hδ, hagree⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hagree)
  obtain ⟨B, _, hB, hBR⟩ := ENNReal.lt_iff_exists_real_btwn.mp hp.r_pos
  have hBpos : 0 < B := ENNReal.ofReal_pos.mp hB
  let ε := min δ B / 4
  have hε : 0 < ε := div_pos (lt_min hδ hBpos) (by norm_num)
  have hεδ : ε < δ := by
    have := min_le_left δ B
    dsimp [ε]
    linarith
  have hεB : 3 * ε < B := by
    have := min_le_right δ B
    dsimp [ε]
    linarith
  have hεR : ENNReal.ofReal (ε + 2 * ε) < R :=
    ((ENNReal.ofReal_lt_ofReal_iff hBpos).mpr (by linarith)).trans hBR
  have hshift : (‖ε‖₊ : ENNReal) < R := by
    change ‖ε‖ₑ < R
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos hε]
    exact (ENNReal.ofReal_le_ofReal (by linarith : ε ≤ ε + 2 * ε)).trans_lt hεR
  have hleft : -(2 * ε) ∈ EMetric.ball (0 : ℝ) (R - ‖ε‖₊) := by
    rw [mem_emetric_ball_zero_iff, lt_tsub_iff_right]
    change ‖-(2 * ε)‖ₑ + ‖ε‖ₑ < R
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_neg,
      abs_of_pos (by linarith : 0 < 2 * ε), abs_of_pos hε, add_comm,
      ← ENNReal.ofReal_add hε.le (by linarith)]
    exact hεR
  let u := σ + ε
  have hu : σ < u := by dsimp [u]; linarith
  have huball : u ∈ Metric.ball σ δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : u - σ = ε := by dsimp [u]; ring
    simpa only [heq, abs_of_pos hε] using hεδ
  have huagree : F =ᶠ[nhds u] mellinTail g a := by
    filter_upwards [Metric.isOpen_ball.mem_nhds huball, Ioi_mem_nhds hu] with v hv hvσ
    exact hagree (Metric.mem_ball.mp hv) hvσ
  have hseries := hp.changeOrigin hshift
  have htaylor := hseries.hasFPowerSeriesAt.eq_formalMultilinearSeries
    hseries.analyticAt.hasFPowerSeriesAt
  have hsum := (hseries.hasSum hleft).summable
  rw [htaylor] at hsum
  refine mellinTail_left_taylor_not_summable g a (σ + ε / 2) u (2 * ε) σ
    ha (by dsimp [u]; linarith) (by linarith) (by dsimp [u]; linarith)
    hg (hupper _ (by linarith)) hnonneg hlower ?_
  convert hsum using 1
  ext n
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, neg_pow (2 * ε) n]
  rw [show σ + ε = u from rfl, huagree.iteratedDeriv_eq n]
  simp only [div_eq_mul_inv]
  ac_rfl

/-- A complex-analytic continuation of the Mellin integral would give a
real-analytic continuation along the real axis. Landau's real obstruction
therefore excludes such a continuation at the abscissa. -/
theorem mellinTail_not_complex_analyticAt_abscissa (g : ℝ → ℝ) (a σ : ℝ)
    (ha : 0 ≤ a) (hg : Measurable g)
    (hnonneg : ∀ t, a ≤ t → 0 ≤ g (Real.exp t))
    (hupper : ∀ s > σ, Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)))
    (hlower : ∀ s : ℝ, Integrable (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t))
      (volume.restrict (Set.Ici a)) → σ ≤ s) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F (σ : ℂ) ∧
      (∀ᶠ v : ℝ in nhdsWithin σ (Set.Ioi σ), F (v : ℂ) =
        ∫ t in Set.Ici a, (g (Real.exp t) : ℂ) * Complex.exp (-(v : ℂ) * (t : ℂ))) := by
  rintro ⟨F, hF, hagree⟩
  apply mellinTail_not_analyticAt_abscissa g a σ ha hg hnonneg hupper hlower
  refine ⟨fun v : ℝ => (F (v : ℂ)).re, ?_, ?_⟩
  · have hreal : AnalyticAt ℝ F (σ : ℂ) := hF.restrictScalars
    have haxis : AnalyticAt ℝ (fun v : ℝ => F (v : ℂ)) σ :=
      hreal.comp (Complex.ofRealCLM.analyticAt σ)
    exact (Complex.reCLM.analyticAt (F (σ : ℂ))).comp
      (f := fun v : ℝ => F (v : ℂ)) haxis
  · filter_upwards [hagree] with v hv
    have hcast : (∫ t in Set.Ici a, (g (Real.exp t) : ℂ) *
        Complex.exp (-(v : ℂ) * (t : ℂ))) = (mellinTail g a v : ℂ) := by
      simp only [mellinTail, ← integral_complex_ofReal, Complex.ofReal_mul,
        Complex.ofReal_exp, Complex.ofReal_neg]
    change (F (v : ℂ)).re = mellinTail g a v
    rw [hv, hcast, Complex.ofReal_re]

#print axioms mellinTail_not_analyticAt_abscissa
#print axioms mellinTail_not_complex_analyticAt_abscissa
end RiemannResearch

namespace RiemannResearch
open MeasureTheory Filter Set Asymptotics

/-- Separate the zero term from the partial sum used by Abel summation. -/
theorem chebyshevPsi_eq_sum_Icc (x : ℝ) :
    chebyshevPsi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [chebyshevPsi, Nat.range_succ_eq_Icc_zero, ← Nat.Icc_insert_succ_left (Nat.zero_le _),
    Finset.sum_insert (by simp)]
  simp

/-- An elementary bound sufficient for absolute convergence to the right of one. -/
theorem chebyshevPsi_bounds (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ chebyshevPsi x ∧ chebyshevPsi x ≤ x * Real.log x := by
  rw [chebyshevPsi_eq_sum_Icc]
  refine ⟨Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg), ?_⟩
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log
        (Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le hn'.1))
        ((Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (zero_le_one.trans hx))))
    _ = (⌊x⌋₊ : ℝ) * Real.log x := by
      simp [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ x * Real.log x :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (zero_le_one.trans hx)) (Real.log_nonneg hx)

/-- The von Mangoldt L-series is the Mellin transform of the real Chebyshev
step function, multiplied by the complex parameter. -/
theorem chebyshevPsi_mellin_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      s * ∫ x in Ioi (1 : ℝ), (chebyshevPsi x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  let ε := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgrowth : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] fun n => (n : ℝ) ^ (1 + ε) := by
    have hlog := (isLittleO_log_rpow_atTop hε).isBigO.natCast_atTop
    have hprod := (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul hlog
    have hbound : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
        =O[atTop] fun n => (n : ℝ) * Real.log n := by
      apply IsBigO.of_bound 1
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      obtain ⟨h0, hb⟩ := chebyshevPsi_bounds (n : ℝ) hn'
      rw [chebyshevPsi_eq_sum_Icc, Nat.floor_natCast] at h0 hb
      rw [one_mul, Real.norm_of_nonneg h0, Real.norm_of_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hn'))]
      exact hb
    refine (hbound.trans hprod).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one]
  have h := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    (show 0 ≤ 1 + ε by linarith) (show 1 + ε < s.re by dsimp [ε]; linarith)
    hgrowth (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  simpa only [chebyshevPsi_eq_sum_Icc, Complex.ofReal_sum] using h

/-- The logarithmic substitution for Mellin integrals on the full ray. -/
theorem mellin_integral_comp_exp (g : ℝ → ℝ) (s : ℂ) :
    (∫ x in Ioi (1 : ℝ), (g x : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      ∫ t in Ici (0 : ℝ), (g (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) := by
  have himage : Real.exp '' Ioi (0 : ℝ) = Ioi (1 : ℝ) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.one_lt_exp_iff.mpr ht
    · intro hx
      have hx' : 0 < x := zero_lt_one.trans hx
      exact ⟨Real.log x, Real.log_pos hx, Real.exp_log hx'⟩
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn,
    integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change |Real.exp t| • ((g (Real.exp t) : ℂ) * (Real.exp t : ℂ) ^ (-(s + 1))) =
    (g (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ))
  rw [abs_of_pos (Real.exp_pos _), Complex.real_smul, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp, Complex.ofReal_exp,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/-- In logarithmic coordinates the Chebyshev Mellin integral is the
negative logarithmic derivative of zeta divided by the parameter. -/
theorem mellin_chebyshevPsi_log (s : ℂ) (hs : 1 < s.re) :
    (∫ t in Ici (0 : ℝ), (chebyshevPsi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ))) =
      (- deriv riemannZeta s / riemannZeta s) / s := by
  have hn : s ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have h := chebyshevPsi_mellin_LSeries s hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, mellin_integral_comp_exp] at h
  exact ((div_eq_iff hn).mpr (h.trans (mul_comm _ _))).symm

/-- The logarithmic-coordinate Chebyshev Mellin integral converges absolutely
throughout the half-plane `1 < s.re`. -/
theorem mellin_chebyshevPsi_log_integrable (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (chebyshevPsi (Real.exp t) : ℂ) *
      Complex.exp (-s * (t : ℂ))) (Ici 0) := by
  let ε := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hmajorant : IntegrableOn (fun t : ℝ => Real.exp ((1 - s.re + ε) * t) / ε) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi.mpr
      (integrableOn_exp_mul_Ioi (a := 1 - s.re + ε) (by dsimp [ε]; linarith) 0)).div_const ε
  have hpsi : Measurable chebyshevPsi :=
    (measurable_of_countable (f := fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k)).comp measurable_id.nat_floor
  apply Integrable.mono hmajorant (((Complex.continuous_ofReal.measurable.comp
    (hpsi.comp Real.continuous_exp.measurable)).mul (by fun_prop)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  obtain ⟨h0, hb⟩ := chebyshevPsi_bounds (Real.exp t) (Real.one_le_exp_iff.mpr ht)
  have ht' : t ≤ Real.exp (ε * t) / ε := (le_div_iff₀ hε).mpr (by
    have hexp := Real.add_one_le_exp (ε * t)
    linarith)
  change ‖(chebyshevPsi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ))‖ ≤
    ‖Real.exp ((1 - s.re + ε) * t) / ε‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, mellin_complex_kernel_norm,
    Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le hε.le)]
  calc
    _ ≤ (Real.exp t * t) * Real.exp (-s.re * t) := by
      rw [Real.log_exp] at hb
      exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = t * Real.exp ((1 - s.re) * t) := by
      rw [mul_comm (Real.exp t) t, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (Real.exp (ε * t) / ε) * Real.exp ((1 - s.re) * t) :=
      mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le
    _ = Real.exp ((1 - s.re + ε) * t) / ε := by
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring

/-- The exponential kernel's half-line Bochner integral, with absolute
convergence supplied by the exponential bound. -/
theorem mellin_complex_integral_Ici (s : ℂ) (a : ℝ) (hs : 0 < s.re) :
    (∫ t in Ici a, Complex.exp (-s * (t : ℂ))) = Complex.exp (-s * (a : ℂ)) / s := by
  rw [integral_Ici_eq_integral_Ioi]
  simpa only [neg_div_neg_eq] using
    integral_exp_mul_complex_Ioi (a := -s) (by simpa only [Complex.neg_re, neg_lt_zero] using hs) a

/-- The full-ray Mellin transform of the adjusted q = 1 prime error
converges absolutely and has the v16 formula on the initial half-plane. -/
theorem adjustedPrimeError_mellin (C θ : ℝ) (s : ℂ) (hθ : θ ≤ 1) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((C * (Real.exp t) ^ θ - primeError (Real.exp t) : ℝ) : ℂ) *
        Complex.exp (-s * (t : ℂ))) (Ici 0) ∧
    (∫ t in Ici (0 : ℝ), ((C * (Real.exp t) ^ θ - primeError (Real.exp t) : ℝ) : ℂ) *
        Complex.exp (-s * (t : ℂ))) =
      (C : ℂ) / (s - (θ : ℂ)) - 1 / (s - 1) + (-deriv riemannZeta s / riemannZeta s) / s := by
  have hkernel (z : ℂ) (hz : 0 < z.re) :
      IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Ici 0) :=
    integrableOn_Ici_iff_integrableOn_Ioi.mpr
      (integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa only [Complex.neg_re, neg_lt_zero] using hz) 0)
  have hθpos : 0 < (s - (θ : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have h1pos : 0 < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hC := (hkernel (s - (θ : ℂ)) hθpos).const_mul (C : ℂ)
  have h1 := hkernel (s - 1) h1pos
  have hψ := mellin_chebyshevPsi_log_integrable s hs
  have hshift (r t : ℝ) : (Real.exp (t * r) : ℂ) * Complex.exp (-s * (t : ℂ)) =
      Complex.exp (-(s - (r : ℂ)) * (t : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, ← Complex.exp_add]
    congr 1
    ring
  have heq (t : ℝ) : ((C * (Real.exp t) ^ θ - primeError (Real.exp t) : ℝ) : ℂ) *
      Complex.exp (-s * (t : ℂ)) =
      (C : ℂ) * Complex.exp (-(s - (θ : ℂ)) * (t : ℂ)) -
        Complex.exp (-(s - 1) * (t : ℂ)) +
        (chebyshevPsi (Real.exp t) : ℂ) * Complex.exp (-s * (t : ℂ)) := by
    have hlinear := hshift 1 t
    simp only [mul_one, Complex.ofReal_one] at hlinear
    simp only [primeError, Complex.ofReal_sub, Complex.ofReal_mul, ← Real.exp_mul,
      sub_mul, mul_assoc, hshift, hlinear]
    abel
  simp_rw [heq]
  refine ⟨(hC.sub h1).add hψ, ?_⟩
  have hadd := integral_add (hC.sub h1) hψ
  have hsub := integral_sub hC h1
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul,
    mellin_complex_integral_Ici _ _ hθpos, mellin_complex_integral_Ici _ _ h1pos,
    mellin_chebyshevPsi_log s hs]
  simp [div_eq_mul_inv]

#print axioms chebyshevPsi_eq_sum_Icc
#print axioms chebyshevPsi_bounds
#print axioms chebyshevPsi_mellin_LSeries
#print axioms mellin_integral_comp_exp
#print axioms mellin_chebyshevPsi_log
#print axioms mellin_chebyshevPsi_log_integrable
#print axioms mellin_complex_integral_Ici
#print axioms adjustedPrimeError_mellin
end RiemannResearch

namespace RiemannResearch
open Filter Set
open scoped Topology

/-- The entire factor of zeta after removing its simple pole at one. -/
noncomputable def regularizedZeta : ℂ → ℂ := by
  classical
  exact Function.update (fun z => (z - 1) * riemannZeta z) 1 1

@[simp]
theorem regularizedZeta_one : regularizedZeta 1 = 1 := by
  simp [regularizedZeta]

theorem regularizedZeta_eventuallyEq (z : ℂ) (hz : z ≠ 1) :
    regularizedZeta =ᶠ[𝓝 z] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact Function.update_of_ne hw _ _

theorem regularizedZeta_analyticAt (z : ℂ) : AnalyticAt ℂ regularizedZeta z := by
  have hd (w : ℂ) (hw : w ≠ 1) : DifferentiableAt ℂ regularizedZeta w :=
    ((differentiableAt_id.sub_const (1 : ℂ)).mul
      (differentiableAt_riemannZeta hw)).congr_of_eventuallyEq (regularizedZeta_eventuallyEq w hw)
  by_cases hz : z = 1
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact hd w hw
    · simpa only [regularizedZeta, continuousAt_update_same] using riemannZeta_residue_one
  · apply DifferentiableOn.analyticAt _ (isOpen_compl_singleton.mem_nhds
      (show z ∈ ({1}ᶜ : Set ℂ) from hz))
    exact fun w hw => (hd w hw).differentiableWithinAt

/-- Off the pole and the zeros, the regularized logarithmic derivative
agrees with the original pair of Mellin terms. -/
theorem regularizedZeta_mellin_eq (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζ : riemannZeta z ≠ 0) :
    -(1 + deriv regularizedZeta z / regularizedZeta z) / z =
      -1 / (z - 1) + (-deriv riemannZeta z / riemannZeta z) / z := by
  have heq := regularizedZeta_eventuallyEq z hz1
  have hsub : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
  have hprod := hsub.mul (differentiableAt_riemannZeta hz1).hasDerivAt
  have hderiv : deriv regularizedZeta z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
    rw [heq.deriv_eq, hprod.deriv, one_mul]
  have hdiff : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  rw [hderiv, heq.eq_of_nhds]
  field_simp
  ring

/-- The two singular terms in the Mellin formula combine to a holomorphic
function at one. The equality specifies its values off the center. -/
theorem riemannZeta_mellin_pole_cancel_one :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      F =ᶠ[𝓝[≠] (1 : ℂ)] fun s =>
        -1 / (s - 1) + (-deriv riemannZeta s / riemannZeta s) / s := by
  have hU := regularizedZeta_analyticAt 1
  have hU1 : regularizedZeta 1 ≠ 0 := by simp
  have hF : AnalyticAt ℂ (fun s => -(1 + deriv regularizedZeta s / regularizedZeta s) / s) 1 :=
    ((analyticAt_const.add (hU.deriv.div hU hU1)).neg).div analyticAt_id one_ne_zero
  refine ⟨_, hF, ?_⟩
  filter_upwards [self_mem_nhdsWithin, (hU.continuousAt.eventually_ne hU1).filter_mono
    nhdsWithin_le_nhds, eventually_ne_nhdsWithin (one_ne_zero : (1 : ℂ) ≠ 0)] with s hs hUs hs0
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    exact hUs (by rw [(regularizedZeta_eventuallyEq s hs).eq_of_nhds, hz, mul_zero])
  exact regularizedZeta_mellin_eq s hs0 hs hζ

/-- The adjusted prime-error Mellin formula admits a holomorphic
representative at one when the exponent is strictly below one. -/
theorem adjustedPrimeError_mellin_removable_one (C θ : ℝ) (hθ : θ < 1) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      F =ᶠ[𝓝[≠] (1 : ℂ)] fun s =>
        (C : ℂ) / (s - (θ : ℂ)) - 1 / (s - 1) + (-deriv riemannZeta s / riemannZeta s) / s := by
  obtain ⟨G, hG, hG_eq⟩ := riemannZeta_mellin_pole_cancel_one
  have hθc : (1 : ℂ) ≠ (θ : ℂ) := by
    intro h
    exact hθ.ne' (by simpa only [Complex.one_re, Complex.ofReal_re] using congrArg Complex.re h)
  refine ⟨fun s => (C : ℂ) / (s - (θ : ℂ)) + G s, ?_, ?_⟩
  · exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hθc)).add hG
  · filter_upwards [hG_eq] with s hs
    rw [hs]
    ring

/-- At a zeta zero away from the other denominators, the Mellin expression
is a simple pole plus an analytic function. Its residue is minus the
positive multiplicity of the zero divided by the zero's location. -/
theorem adjustedPrimeError_mellin_at_zeta_zero (C θ : ℝ) (ρ : ℂ)
    (hρ : riemannZeta ρ = 0) (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hρθ : ρ ≠ (θ : ℂ)) :
    ∃ (m : ℕ) (H : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ H ρ ∧
      (∀ᶠ s in 𝓝[≠] ρ, (C : ℂ) / (s - (θ : ℂ)) - 1 / (s - 1) +
        (-deriv riemannZeta s / riemannZeta s) / s =
          (-(m : ℂ) / ρ) / (s - ρ) + H s) := by
  have hζa : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
    intro z hz
    apply DifferentiableOn.analyticAt _ (isOpen_compl_singleton.mem_nhds hz)
    intro w hw
    exact (differentiableAt_riemannZeta hw).differentiableWithinAt
  have hρmem : ρ ∈ ({1}ᶜ : Set ℂ) := hρ1
  have hζloc : ¬ riemannZeta =ᶠ[𝓝 ρ] (0 : ℂ → ℂ) := by
    intro hzero
    have hc : IsPreconnected ({1}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    have hz2 := hζa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρmem hzero
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 : ℂ).re) hz2
  obtain ⟨m, G, hG, hG0, heq⟩ :=
    (hζa ρ hρmem).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hζloc
  simp only [smul_eq_mul] at heq
  change riemannZeta =ᶠ[𝓝 ρ] (fun z => (z - ρ) ^ m * G z) at heq
  have hm : m ≠ 0 := by
    intro hm
    have h := heq.eq_of_nhds
    simp [hρ, hm] at h
    exact hG0 h.symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  let H : ℂ → ℂ := fun s => (C : ℂ) / (s - (θ : ℂ)) - 1 / (s - 1) +
    (-(deriv G s / G s)) / s + ((k + 1 : ℕ) : ℂ) / (s * ρ)
  have hH : AnalyticAt ℂ H ρ := by
    exact (((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hρθ)).sub
      (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hρ1))).add
      ((hG.deriv.div hG hG0).neg.div analyticAt_id hρ0)).add
      (analyticAt_const.div (analyticAt_id.mul analyticAt_const) (mul_ne_zero hρ0 hρ0))
  refine ⟨k + 1, H, Nat.succ_pos k, hH, ?_⟩
  filter_upwards [self_mem_nhdsWithin, heq.eventuallyEq_nhds.filter_mono nhdsWithin_le_nhds,
    (hG.continuousAt.eventually_ne hG0).filter_mono nhdsWithin_le_nhds,
    (hG.eventually_analyticAt).filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin hρ0] with s hs hseq hGs hGa hs0
  have hdiff : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hsub : HasDerivAt (fun z : ℂ => z - ρ) 1 s := (hasDerivAt_id s).sub_const ρ
  have hprod := (hsub.pow (k + 1)).mul hGa.differentiableAt.hasDerivAt
  have hlog : -deriv riemannZeta s / riemannZeta s =
      -((k + 1 : ℕ) : ℂ) / (s - ρ) - deriv G s / G s := by
    rw [hseq.deriv_eq, hprod.deriv, hseq.eq_of_nhds]
    simp only [Nat.add_sub_cancel, mul_one, pow_succ]
    field_simp
    ring
  dsimp only [H]
  rw [hlog]
  field_simp
  ring

#print axioms riemannZeta_mellin_pole_cancel_one
#print axioms adjustedPrimeError_mellin_removable_one
#print axioms adjustedPrimeError_mellin_at_zeta_zero
end RiemannResearch

namespace RiemannResearch
open MeasureTheory Filter Set

/-- The complex Mellin transform in logarithmic coordinates on a specified set. -/
noncomputable def complexMellinOn (g : ℝ → ℝ) (S : Set ℝ) (z : ℂ) : ℂ :=
  ∫ t in S, (g (Real.exp t) : ℂ) * Complex.exp (-z * (t : ℂ))

/-- The absolute convergence test for a complex kernel only involves the real part. -/
theorem complexMellinOn_integrable_iff (g : ℝ → ℝ) (S : Set ℝ) (z : ℂ)
    (hg : Measurable g) :
    IntegrableOn (fun t : ℝ => (g (Real.exp t) : ℂ) * Complex.exp (-z * (t : ℂ))) S ↔
      IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-z.re * t)) S := by
  have hmeas := hg.comp Real.continuous_exp.measurable
  have hc : Measurable (fun t : ℝ => (g (Real.exp t) : ℂ) * Complex.exp (-z * (t : ℂ))) :=
    (Complex.continuous_ofReal.measurable.comp hmeas).mul (by fun_prop)
  have hr : Measurable (fun t : ℝ => g (Real.exp t) * Real.exp (-z.re * t)) :=
    hmeas.mul (by fun_prop)
  change Integrable _ (volume.restrict S) ↔ Integrable _ (volume.restrict S)
  rw [← integrable_norm_iff hc.aestronglyMeasurable, ← integrable_norm_iff hr.aestronglyMeasurable]
  simp only [norm_mul, Complex.norm_real, mellin_complex_kernel_norm,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]

/-- Integrability of the zeroth and first moments at a real parameter
gives holomorphy to its right on a nonnegative domain of integration. -/
theorem complexMellinOn_analyticOnNhd (g : ℝ → ℝ) (S : Set ℝ) (v : ℝ)
    (hS : MeasurableSet S) (hS0 : S ⊆ Ici 0) (hg : Measurable g)
    (h0 : IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-v * t)) S)
    (h1 : IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-v * t) * t) S) :
    AnalyticOnNhd ℂ (complexMellinOn g S) {z : ℂ | v < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  change v < z.re at hz
  let μ := volume.restrict S
  let F (w : ℂ) (t : ℝ) := (g (Real.exp t) : ℂ) * Complex.exp (-w * (t : ℂ))
  let D (w : ℂ) (t : ℝ) := F w t * (-(t : ℂ))
  have hFmeas (w : ℂ) : Measurable (F w) :=
    (Complex.continuous_ofReal.measurable.comp (hg.comp Real.continuous_exp.measurable)).mul
      (by fun_prop)
  have hDom (t : ℝ) (ht : t ∈ S) (w : ℂ) (hw : v ≤ w.re) :
      ‖F w t‖ ≤ ‖g (Real.exp t) * Real.exp (-v * t)‖ := by
    simp only [F, norm_mul, Complex.norm_real, mellin_complex_kernel_norm,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (mellin_kernel_le t v w.re (hS0 ht) hw) (norm_nonneg _)
  have hFi : Integrable (F z) μ := by
    apply Integrable.mono h0 (hFmeas z).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS] with t ht
    exact hDom t ht z hz.le
  have hDm : AEStronglyMeasurable (D z) μ :=
    ((hFmeas z).mul (Complex.continuous_ofReal.neg.measurable)).aestronglyMeasurable
  have hBd : ∀ᵐ t ∂μ, ∀ w ∈ Metric.ball z (z.re - v),
      ‖D w t‖ ≤ ‖g (Real.exp t) * Real.exp (-v * t) * t‖ := by
    filter_upwards [ae_restrict_mem hS] with t ht w hw
    have hdist : ‖w - z‖ < z.re - v := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hre : -(z.re - v) < (w - z).re :=
      neg_lt_of_abs_lt ((Complex.abs_re_le_norm _).trans_lt hdist)
    rw [Complex.sub_re] at hre
    dsimp only [D]
    rw [norm_mul (F w t), norm_neg, Complex.norm_real,
      norm_mul (g (Real.exp t) * Real.exp (-v * t)) t]
    exact mul_le_mul_of_nonneg_right (hDom t ht w (by linarith)) (norm_nonneg t)
  have hdiff (t : ℝ) (w : ℂ) : HasDerivAt (fun u => F u t) (D w t) w := by
    have h := (((hasDerivAt_id w).neg.mul_const (t : ℂ)).cexp.const_mul
      (g (Real.exp t) : ℂ))
    simpa only [F, D, id_eq, neg_one_mul, mul_assoc] using h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (sub_pos.mpr hz)
    (Eventually.of_forall fun w => (hFmeas w).aestronglyMeasurable) hFi hDm hBd h1.norm
    (Eventually.of_forall fun t w _ => hdiff t w)).2.differentiableAt.differentiableWithinAt

/-- On a compact initial segment, every exponential moment is integrable
once a single exponential weight is integrable. -/
theorem mellin_prefix_moment_integrable (g : ℝ → ℝ) (a r v : ℝ) (k : ℕ)
    (hi : IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-r * t)) (Ico 0 a)) :
    IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-v * t) * t ^ k) (Ico 0 a) := by
  let w : ℝ → ℝ := fun t => Real.exp ((r - v) * t) * t ^ k
  have hw : Continuous w := by dsimp [w]; fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw.continuousOn (s := Icc 0 a)
  have hbound : ∀ᵐ t ∂volume.restrict (Ico (0 : ℝ) a), ‖w t‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact hM t (Ico_subset_Icc_self ht)
  apply (hi.bdd_mul' hw.measurable.aestronglyMeasurable hbound).congr
  apply Eventually.of_forall
  intro t
  dsimp [w]
  calc
    _ = g (Real.exp t) * (Real.exp ((r - v) * t) * Real.exp (-r * t)) * t ^ k := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 3
      ring

/-- The finite prefix of the logarithmic-coordinate Mellin transform is entire. -/
theorem complexMellinOn_prefix_entire (g : ℝ → ℝ) (a r : ℝ) (hg : Measurable g)
    (hi : IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-r * t)) (Ico 0 a)) :
    ∀ z : ℂ, AnalyticAt ℂ (complexMellinOn g (Ico 0 a)) z := by
  intro z
  apply complexMellinOn_analyticOnNhd g (Ico 0 a) (z.re - 1) measurableSet_Ico
    (fun _ ht => ht.1) hg
  · simpa using mellin_prefix_moment_integrable g a r (z.re - 1) 0 hi
  · simpa using mellin_prefix_moment_integrable g a r (z.re - 1) 1 hi
  · show z.re - 1 < z.re
    linarith

/-- The complex tail is holomorphic strictly to the right of every
absolutely convergent real parameter. -/
theorem complexMellinOn_tail_analyticOnNhd (g : ℝ → ℝ) (a s : ℝ) (ha : 0 ≤ a) (hg : Measurable g)
    (hi : IntegrableOn (fun t : ℝ => g (Real.exp t) * Real.exp (-s * t)) (Ici a)) :
    AnalyticOnNhd ℂ (complexMellinOn g (Ici a)) {z : ℂ | s < z.re} := by
  intro z hz
  change s < z.re at hz
  let v := (s + z.re) / 2
  have hsv : s < v := by dsimp [v]; linarith
  have hvz : v < z.re := by dsimp [v]; linarith
  apply complexMellinOn_analyticOnNhd g (Ici a) v measurableSet_Ici (fun _ ht => ha.trans ht) hg
  · exact mellin_integrable_right g a s v ha hsv.le hg hi
  · simpa using mellin_moments_inside g a s v 1 ha hsv hg hi
  · exact hvz

/-- The adjustment to the prime error used in the one-sided criterion. -/
noncomputable def adjustedPrimeError (C θ x : ℝ) : ℝ := C * x ^ θ - primeError x

theorem measurable_adjustedPrimeError (C θ : ℝ) : Measurable (adjustedPrimeError C θ) := by
  have hpsi : Measurable chebyshevPsi :=
    (measurable_of_countable (f := fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.vonMangoldt k)).comp measurable_id.nat_floor
  exact (measurable_id.pow_const θ |>.const_mul C).sub (measurable_id.sub hpsi)

/-- A one-sided prime-error bound supplies a nonnegative tail and an
entire prefix whose transforms add to the explicit formula on the
initial half-plane. The tail converges absolutely there. -/
theorem adjustedPrimeError_mellin_tail_split (θ : ℝ) (hθ : θ ≤ 1) (h : OneSidedBound θ) :
    ∃ C a : ℝ, 0 ≤ a ∧
      (∀ t ≥ a, 0 ≤ adjustedPrimeError C θ (Real.exp t)) ∧
      (∀ z : ℂ, AnalyticAt ℂ (complexMellinOn (adjustedPrimeError C θ) (Ico 0 a)) z) ∧
      ∀ z : ℂ, 1 < z.re →
        IntegrableOn (fun t : ℝ => adjustedPrimeError C θ (Real.exp t) *
          Real.exp (-z.re * t)) (Ici a) ∧
        complexMellinOn (adjustedPrimeError C θ) (Ico 0 a) z +
          complexMellinOn (adjustedPrimeError C θ) (Ici a) z =
            (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
              (-deriv riemannZeta z / riemannZeta z) / z := by
  obtain ⟨C, x₀, _, hx₀, hbound⟩ := h
  let a := Real.log x₀
  have ha : 0 ≤ a := Real.log_nonneg hx₀
  let g := adjustedPrimeError C θ
  have hg : Measurable g := measurable_adjustedPrimeError C θ
  have h0a : Ico (0 : ℝ) a ⊆ Ici 0 := fun _ ht => ht.1
  have haa : Ici a ⊆ Ici 0 := Ici_subset_Ici.mpr ha
  have hi := (complexMellinOn_integrable_iff g (Ici 0) (2 : ℂ) hg).mp
    (adjustedPrimeError_mellin C θ 2 hθ (by norm_num)).1
  refine ⟨C, a, ha, ?_, complexMellinOn_prefix_entire g a _ hg (hi.mono_set h0a), ?_⟩
  · intro t ht
    have htx : x₀ ≤ Real.exp t := (Real.exp_log (zero_lt_one.trans_le hx₀)).symm.le.trans
      (Real.exp_le_exp.mpr ht)
    exact sub_nonneg.mpr (hbound _ htx)
  · intro z hz
    have hfull := adjustedPrimeError_mellin C θ z hθ hz
    have htail := hfull.1.mono_set haa
    have hprefix := hfull.1.mono_set h0a
    refine ⟨(complexMellinOn_integrable_iff g (Ici a) z hg).mp htail, ?_⟩
    have hd : Disjoint (Ico (0 : ℝ) a) (Ici a) :=
      Set.disjoint_left.mpr fun _ ht₁ ht₂ => not_lt_of_ge ht₂ ht₁.2
    unfold complexMellinOn adjustedPrimeError
    rw [← setIntegral_union hd measurableSet_Ici hprefix htail, Ico_union_Ici_eq_Ici ha]
    exact hfull.2

#print axioms complexMellinOn_integrable_iff
#print axioms complexMellinOn_analyticOnNhd
#print axioms mellin_prefix_moment_integrable
#print axioms complexMellinOn_prefix_entire
#print axioms complexMellinOn_tail_analyticOnNhd
#print axioms measurable_adjustedPrimeError
#print axioms adjustedPrimeError_mellin_tail_split
end RiemannResearch

namespace RiemannResearch
open Filter Set
open scoped Topology

/-- Clearing the denominators lets the Mellin identity propagate across
the whole convergence half-plane, including at the zeros of the factors. -/
theorem adjustedPrimeError_mellin_cleared_identity (C θ σ : ℝ) (hθ : θ ≤ 1) (hσ : σ ≤ 1)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {z : ℂ | σ < z.re})
    (hinit : ∀ z : ℂ, 1 < z.re →
      F z = (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
        (-deriv riemannZeta z / riemannZeta z) / z) :
    EqOn (fun z => z * (z - (θ : ℂ)) * regularizedZeta z * F z)
      (fun z => (C : ℂ) * z * regularizedZeta z -
        (z - (θ : ℂ)) * (regularizedZeta z + deriv regularizedZeta z))
      {z : ℂ | σ < z.re} := by
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (2 : ℂ))
  · intro z hz
    exact (((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
      (regularizedZeta_analyticAt z)).mul (hF z hz))
  · intro z _
    exact ((analyticAt_const.mul analyticAt_id).mul (regularizedZeta_analyticAt z)).sub
      ((analyticAt_id.sub analyticAt_const).mul
        ((regularizedZeta_analyticAt z).add (regularizedZeta_analyticAt z).deriv))
  · exact (convex_halfSpace_re_gt σ).isPreconnected
  · change σ < (2 : ℂ).re
    exact hσ.trans_lt (by norm_num)
  · have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with z hz
    change 1 < z.re at hz
    have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hz)
    have hz1 : z ≠ 1 := by
      intro h
      simp [h] at hz
    have hzθ : z - (θ : ℂ) ≠ 0 := sub_ne_zero.mpr (by
      intro h
      exact (not_lt_of_ge hθ) (by simpa [h] using hz))
    have hζ := riemannZeta_ne_zero_of_one_le_re hz.le
    have hU : regularizedZeta z ≠ 0 := by
      rw [(regularizedZeta_eventuallyEq z hz1).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) hζ
    have hinit' : F z = (C : ℂ) / (z - (θ : ℂ)) -
        (1 + deriv regularizedZeta z / regularizedZeta z) / z := by
      rw [hinit z hz]
      linear_combination -(regularizedZeta_mellin_eq z hz0 hz1 hζ)
    change z * (z - (θ : ℂ)) * regularizedZeta z * F z =
      (C : ℂ) * z * regularizedZeta z -
        (z - (θ : ℂ)) * (regularizedZeta z + deriv regularizedZeta z)
    rw [hinit']
    field_simp
    ring

/-- Recover the regularized Mellin formula on the convergence half-plane
where the recovered expression has nonzero denominators. -/
theorem adjustedPrimeError_mellin_continuation (C θ σ : ℝ) (hθ : θ ≤ 1) (hσ : σ ≤ 1)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {z : ℂ | σ < z.re})
    (hinit : ∀ z : ℂ, 1 < z.re →
      F z = (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
        (-deriv riemannZeta z / riemannZeta z) / z)
    (z : ℂ) (hz : σ < z.re) (hz0 : z ≠ 0) (hzθ : z ≠ (θ : ℂ))
    (hU : regularizedZeta z ≠ 0) :
    F z = (C : ℂ) / (z - (θ : ℂ)) - (1 + deriv regularizedZeta z / regularizedZeta z) / z := by
  have hid := adjustedPrimeError_mellin_cleared_identity C θ σ hθ hσ F hF hinit hz
  have hdθ : z - (θ : ℂ) ≠ 0 := sub_ne_zero.mpr hzθ
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hz0 hdθ) hU)
  change z * (z - (θ : ℂ)) * regularizedZeta z * F z = _ at hid
  rw [hid]
  field_simp
  ring

/-- The regularized identity applies to the sum of the entire prefix and
the tail on its open half-plane of absolute convergence. -/
theorem adjustedPrimeError_split_mellin_cleared_identity (C θ a σ : ℝ)
    (hθ : θ ≤ 1) (hσ : σ ≤ 1) (ha : 0 ≤ a)
    (hprefix : ∀ z : ℂ, AnalyticAt ℂ (complexMellinOn (adjustedPrimeError C θ) (Ico 0 a)) z)
    (htail : ∀ s > σ, MeasureTheory.IntegrableOn (fun t : ℝ =>
      adjustedPrimeError C θ (Real.exp t) * Real.exp (-s * t)) (Ici a))
    (hinit : ∀ z : ℂ, 1 < z.re →
      complexMellinOn (adjustedPrimeError C θ) (Ico 0 a) z +
        complexMellinOn (adjustedPrimeError C θ) (Ici a) z =
          (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
            (-deriv riemannZeta z / riemannZeta z) / z) :
    EqOn (fun z => z * (z - (θ : ℂ)) * regularizedZeta z *
      (complexMellinOn (adjustedPrimeError C θ) (Ico 0 a) z +
        complexMellinOn (adjustedPrimeError C θ) (Ici a) z))
      (fun z => (C : ℂ) * z * regularizedZeta z -
        (z - (θ : ℂ)) * (regularizedZeta z + deriv regularizedZeta z))
      {z : ℂ | σ < z.re} := by
  apply adjustedPrimeError_mellin_cleared_identity C θ σ hθ hσ _ _ hinit
  intro z hz
  change σ < z.re at hz
  let v := (σ + z.re) / 2
  have hσv : σ < v := by dsimp [v]; linarith
  have hvz : v < z.re := by dsimp [v]; linarith
  exact (hprefix z).add (complexMellinOn_tail_analyticOnNhd (adjustedPrimeError C θ)
    a v ha (measurable_adjustedPrimeError C θ) (htail v hσv) z hvz)

#print axioms regularizedZeta_one
#print axioms regularizedZeta_eventuallyEq
#print axioms regularizedZeta_analyticAt
#print axioms regularizedZeta_mellin_eq
#print axioms adjustedPrimeError_mellin_cleared_identity
#print axioms adjustedPrimeError_mellin_continuation
#print axioms adjustedPrimeError_split_mellin_cleared_identity
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Topology

/-- The entire zeta factor has isolated zeros, since it is one at one. -/
theorem regularizedZeta_eventually_ne_zero (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, regularizedZeta w ≠ 0 := by
  rcases (regularizedZeta_analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have han : AnalyticOnNhd ℂ regularizedZeta (univ : Set ℂ) :=
      fun w _ => regularizedZeta_analyticAt w
    have hEq : regularizedZeta =ᶠ[𝓝 z] (0 : ℂ → ℂ) := h
    have hz := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) hEq (mem_univ (1 : ℂ))
    simp at hz
  · exact h

/-- Negative real residue gives divergence to minus infinity from the right,
even after adding a term continuous at the pole. -/
theorem negative_real_pole_tendsto_atBot (σ c : ℝ) (hc : c < 0) (G : ℝ → ℝ)
    (hG : ContinuousAt G σ) :
    Tendsto (fun t => c / (t - σ) + G t) (𝓝[>] σ) atBot := by
  have hsub : Tendsto (fun t : ℝ => t - σ) (𝓝[>] σ) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using ((continuous_id.sub continuous_const).continuousAt :
        ContinuousAt (fun t : ℝ => t - σ) σ).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact show t - σ ∈ Ioi 0 from sub_pos.mpr (show σ < t from ht)
  have hsing := (tendsto_inv_nhdsGT_zero.comp hsub).const_mul_atTop_of_neg hc
  simpa only [div_eq_mul_inv, Function.comp_apply] using
    hsing.atBot_add (hG.tendsto.mono_left nhdsWithin_le_nhds)

/-- For a finite convergence abscissa, the Landau obstruction and the sign of
the residue force the abscissa to lie at or to the left of the exponent. -/
theorem adjustedPrimeError_abscissa_le (C θ a σ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hσ : σ ≤ 1) (ha : 0 ≤ a)
    (hnonneg : ∀ t ≥ a, 0 ≤ adjustedPrimeError C θ (Real.exp t))
    (hprefix : ∀ z : ℂ, AnalyticAt ℂ (complexMellinOn (adjustedPrimeError C θ) (Ico 0 a)) z)
    (hupper : ∀ s > σ, IntegrableOn (fun t : ℝ =>
      adjustedPrimeError C θ (Real.exp t) * Real.exp (-s * t)) (Ici a))
    (hlower : ∀ s : ℝ, IntegrableOn (fun t : ℝ =>
      adjustedPrimeError C θ (Real.exp t) * Real.exp (-s * t)) (Ici a) → σ ≤ s)
    (hinit : ∀ z : ℂ, 1 < z.re →
      complexMellinOn (adjustedPrimeError C θ) (Ico 0 a) z +
        complexMellinOn (adjustedPrimeError C θ) (Ici a) z =
        (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
          (-deriv riemannZeta z / riemannZeta z) / z) :
    σ ≤ θ := by
  by_contra! hθσ
  let g := adjustedPrimeError C θ
  let P := complexMellinOn g (Ico 0 a)
  let T := complexMellinOn g (Ici a)
  let F := fun z => P z + T z
  let R := fun z : ℂ => (C : ℂ) / (z - (θ : ℂ)) -
    (1 + deriv regularizedZeta z / regularizedZeta z) / z
  have hg := measurable_adjustedPrimeError C θ
  have hF : AnalyticOnNhd ℂ F {z : ℂ | σ < z.re} := by
    intro z hz
    change σ < z.re at hz
    let v := (σ + z.re) / 2
    have hsv : σ < v := by dsimp [v]; linarith
    have hvz : v < z.re := by dsimp [v]; linarith
    exact (hprefix z).add (complexMellinOn_tail_analyticOnNhd g a v ha hg (hupper v hsv) z hvz)
  have hσpos : 0 < σ := hθ0.trans_lt hθσ
  have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσpos.ne'
  have hσθ : (σ : ℂ) ≠ (θ : ℂ) := fun h => hθσ.ne' (Complex.ofReal_injective h)
  have haxis : Tendsto (fun v : ℝ => (v : ℂ)) (𝓝[>] σ) (𝓝[≠] (σ : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with v hv
    exact fun heq => (show σ < v from hv).ne' (Complex.ofReal_injective heq)
  have hFR : ∀ᶠ v : ℝ in 𝓝[>] σ, F (v : ℂ) = R (v : ℂ) := by
    filter_upwards [self_mem_nhdsWithin, haxis.eventually (regularizedZeta_eventually_ne_zero (σ : ℂ))]
      with v hv hUv
    have hv' : σ < v := hv
    exact adjustedPrimeError_mellin_continuation C θ σ hθ.le hσ F hF hinit _
      (by simpa using hv') (Complex.ofReal_ne_zero.mpr (hσpos.trans hv').ne')
      (fun h => (hθσ.trans hv').ne' (Complex.ofReal_injective h)) hUv
  by_cases hUσ : regularizedZeta (σ : ℂ) = 0
  · have hσ1 : (σ : ℂ) ≠ 1 := fun h => by rw [h, regularizedZeta_one] at hUσ; exact one_ne_zero hUσ
    have hζσ : riemannZeta (σ : ℂ) = 0 := by
      rw [(regularizedZeta_eventuallyEq (σ : ℂ) hσ1).eq_of_nhds] at hUσ
      exact (mul_eq_zero.mp hUσ).resolve_left (sub_ne_zero.mpr hσ1)
    obtain ⟨m, H, hm, hH, hlocal⟩ :=
      adjustedPrimeError_mellin_at_zeta_zero C θ (σ : ℂ) hζσ hσ0 hσ1 hσθ
    have hTlocal : ∀ᶠ v : ℝ in 𝓝[>] σ,
        (T (v : ℂ)).re = -(m : ℝ) / σ / (v - σ) + (H (v : ℂ) - P (v : ℂ)).re := by
      filter_upwards [hFR, haxis.eventually hlocal, haxis.eventually
        (eventually_ne_nhdsWithin hσ1), self_mem_nhdsWithin, haxis.eventually
        (regularizedZeta_eventually_ne_zero (σ : ℂ))] with v hvR hvH hv1 hv hUv
      have hv' : σ < v := hv
      have hv0 := Complex.ofReal_ne_zero.mpr (hσpos.trans hv').ne'
      have hvζ : riemannZeta (v : ℂ) ≠ 0 := by
        intro h
        exact hUv (by rw [(regularizedZeta_eventuallyEq _ hv1).eq_of_nhds, h, mul_zero])
      have he : R (v : ℂ) = (C : ℂ) / ((v : ℂ) - (θ : ℂ)) - 1 / ((v : ℂ) - 1) +
          (-deriv riemannZeta (v : ℂ) / riemannZeta (v : ℂ)) / (v : ℂ) := by
        dsimp [R]
        linear_combination regularizedZeta_mellin_eq (v : ℂ) hv0 hv1 hvζ
      have hre := congrArg Complex.re (hvR.trans (he.trans hvH))
      have hrealPole : ((-(m : ℂ) / (σ : ℂ)) / ((v : ℂ) - (σ : ℂ))).re =
          -(m : ℝ) / σ / (v - σ) := by
        exact_mod_cast (Complex.ofReal_re (-(m : ℝ) / σ / (v - σ)))
      change (P (v : ℂ) + T (v : ℂ)).re = _ at hre
      simp only [Complex.add_re, hrealPole] at hre
      rw [Complex.sub_re]
      linarith
    have hcont : ContinuousAt (fun v : ℝ => (H (v : ℂ) - P (v : ℂ)).re) σ :=
      Complex.continuous_re.continuousAt.comp
        ((hH.continuousAt.sub (hprefix (σ : ℂ)).continuousAt).comp Complex.continuous_ofReal.continuousAt)
    have hneg : -(m : ℝ) / σ < 0 := div_neg_of_neg_of_pos (neg_lt_zero.mpr (by exact_mod_cast hm)) hσpos
    have hlim := (negative_real_pole_tendsto_atBot σ _ hneg _ hcont).congr' (hTlocal.mono fun _ h => h.symm)
    have hTpos : ∀ᶠ v : ℝ in 𝓝[>] σ, 0 ≤ (T (v : ℂ)).re := by
      apply Eventually.of_forall
      intro v
      have heq : T (v : ℂ) = (mellinTail g a v : ℂ) := by
        simp only [T, complexMellinOn, mellinTail, ← integral_complex_ofReal, Complex.ofReal_mul,
          Complex.ofReal_exp, Complex.ofReal_neg]
      rw [heq, Complex.ofReal_re]
      exact mellinTail_nonneg g a v hnonneg
    obtain ⟨v, hv₁, hv₂⟩ := ((tendsto_atBot.mp hlim (-1)).and hTpos).exists
    linarith
  · have hRa : AnalyticAt ℂ R (σ : ℂ) := by
      have hU := regularizedZeta_analyticAt (σ : ℂ)
      exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hσθ)).sub
        ((analyticAt_const.add (hU.deriv.div hU hUσ)).div analyticAt_id hσ0)
    apply mellinTail_not_complex_analyticAt_abscissa g a σ ha hg hnonneg hupper hlower
    refine ⟨fun z => R z - P z, hRa.sub (hprefix (σ : ℂ)), ?_⟩
    filter_upwards [hFR] with v hv
    change R (v : ℂ) - P (v : ℂ) = T (v : ℂ)
    exact sub_eq_iff_eq_add.mpr (hv.symm.trans (add_comm _ _))

/-- A one-sided bound gives absolute convergence of the adjusted Mellin
tail throughout the open half-plane to the right of the bound's exponent.
The witnesses retain their nonnegative tail and the Mellin identity. -/
theorem adjustedPrimeError_tail_converges (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (h : OneSidedBound θ) :
    ∃ C a : ℝ, 0 ≤ a ∧
      (∀ t ≥ a, 0 ≤ adjustedPrimeError C θ (Real.exp t)) ∧
      (∀ z : ℂ, AnalyticAt ℂ (complexMellinOn (adjustedPrimeError C θ) (Ico 0 a)) z) ∧
      (∀ s > θ, IntegrableOn (fun t : ℝ => adjustedPrimeError C θ (Real.exp t) *
        Real.exp (-s * t)) (Ici a)) ∧
      ∀ z : ℂ, 1 < z.re →
        complexMellinOn (adjustedPrimeError C θ) (Ico 0 a) z +
          complexMellinOn (adjustedPrimeError C θ) (Ici a) z =
          (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
            (-deriv riemannZeta z / riemannZeta z) / z := by
  obtain ⟨C, a, ha, hnonneg, hprefix, hinit⟩ := adjustedPrimeError_mellin_tail_split θ hθ.le h
  have hformula (z : ℂ) (hz : 1 < z.re) := (hinit z hz).2
  refine ⟨C, a, ha, hnonneg, hprefix, ?_, hformula⟩
  intro v hv
  by_contra hnot
  let A : Set ℝ := {s | IntegrableOn (fun t : ℝ => adjustedPrimeError C θ (Real.exp t) *
    Real.exp (-s * t)) (Ici a)}
  have hmem (s : ℝ) (hs : 1 < s) : s ∈ A := by
    simpa only [Complex.ofReal_re] using (hinit (s : ℂ) (by simpa only [Complex.ofReal_re])).1
  have hA : A.Nonempty := ⟨2, hmem 2 (by norm_num)⟩
  have hb (s : ℝ) (hs : s ∈ A) : v ≤ s := by
    by_contra! hlt
    exact hnot (mellin_integrable_right (adjustedPrimeError C θ) a s v ha hlt.le
      (measurable_adjustedPrimeError C θ) hs)
  have hbdd : BddBelow A := ⟨v, fun s hs => hb s hs⟩
  let σ := sInf A
  have hvσ : v ≤ σ := le_csInf hA (fun s hs => hb s hs)
  have hσ : σ ≤ 1 := by
    by_contra! hlt
    let w := (1 + σ) / 2
    have hw₁ : 1 < w := by dsimp [w]; linarith
    have hw₂ : w < σ := by dsimp [w]; linarith
    exact (not_le_of_gt hw₂) (csInf_le hbdd (hmem w hw₁))
  have hupper (s : ℝ) (hs : σ < s) : s ∈ A := by
    obtain ⟨r, hr, hrs⟩ := exists_lt_of_csInf_lt hA hs
    exact mellin_integrable_right (adjustedPrimeError C θ) a r s ha hrs.le
      (measurable_adjustedPrimeError C θ) hr
  have hσθ := adjustedPrimeError_abscissa_le C θ a σ hθ0 hθ hσ ha hnonneg hprefix
    hupper (fun s hs => csInf_le hbdd hs) hformula
  exact (not_le_of_gt (hv.trans_le hvσ)) hσθ

/-- A holomorphic representative of the Mellin formula rules out poles
from zeta zeros throughout its right half-plane. -/
theorem riemannZeta_ne_zero_of_analytic_mellin_formula (C θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {z : ℂ | θ < z.re})
    (hinit : ∀ z : ℂ, 1 < z.re →
      F z = (C : ℂ) / (z - (θ : ℂ)) - 1 / (z - 1) +
        (-deriv riemannZeta z / riemannZeta z) / z)
    (ρ : ℂ) (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hzero
  have hρ0 : ρ ≠ 0 := Complex.ne_zero_of_re_pos (hθ0.trans_lt hρ)
  have hρ1 : ρ ≠ 1 := fun he => riemannZeta_ne_zero_of_one_le_re (by simp [he]) hzero
  have hρθ : ρ ≠ (θ : ℂ) := fun he => by simp [he] at hρ
  obtain ⟨m, H, hm, hH, hlocal⟩ :=
    adjustedPrimeError_mellin_at_zeta_zero C θ ρ hzero hρ0 hρ1 hρθ
  have hnear : ∀ᶠ z in 𝓝 ρ, θ < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hρ
  have hprod : (fun z => (z - ρ) * (F z - H z)) =ᶠ[𝓝[≠] ρ] fun _ => -(m : ℂ) / ρ := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, hlocal, regularizedZeta_eventually_ne_zero ρ,
      eventually_ne_nhdsWithin hρ1, self_mem_nhdsWithin] with z hz hHl hUz hz1 hzρ
    have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos (hθ0.trans_lt hz)
    have hzθ : z ≠ (θ : ℂ) := fun he => by simp [he] at hz
    have hzζ : riemannZeta z ≠ 0 := by
      intro he
      exact hUz (by rw [(regularizedZeta_eventuallyEq z hz1).eq_of_nhds, he, mul_zero])
    have he := adjustedPrimeError_mellin_continuation C θ θ hθ hθ F hF hinit z hz hz0 hzθ hUz
    have he' : F z = -(m : ℂ) / ρ / (z - ρ) + H z := by
      rw [← hHl, he]
      linear_combination regularizedZeta_mellin_eq z hz0 hz1 hzζ
    have hd : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    change (z - ρ) * (F z - H z) = -(m : ℂ) / ρ
    rw [he', add_sub_cancel_right, mul_comm, div_mul_cancel₀ _ hd]
  have hlim : Tendsto (fun z => (z - ρ) * (F z - H z)) (𝓝[≠] ρ) (𝓝 (0 : ℂ)) := by
    have hc : ContinuousAt (fun z => (z - ρ) * (F z - H z)) ρ :=
      (continuous_id.sub continuous_const).continuousAt.mul
        ((hF ρ hρ).continuousAt.sub hH.continuousAt)
    simpa only [sub_self, zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hh := tendsto_nhds_unique (hlim.congr' hprod) tendsto_const_nhds
  exact (div_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hm.ne')) hρ0) hh.symm

/-- The forward direction of the v16 one-sided criterion at q = 1:
a one-sided bound at exponent θ excludes every zeta zero to its right. -/
theorem riemannZeta_ne_zero_of_oneSidedBound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (h : OneSidedBound θ) (ρ : ℂ) (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  obtain ⟨C, a, ha, _, hprefix, htail, hinit⟩ := adjustedPrimeError_tail_converges θ hθ0 hθ h
  let P := complexMellinOn (adjustedPrimeError C θ) (Ico 0 a)
  let T := complexMellinOn (adjustedPrimeError C θ) (Ici a)
  let F := fun z => P z + T z
  have hF : AnalyticOnNhd ℂ F {z : ℂ | θ < z.re} := by
    intro z hz
    change θ < z.re at hz
    let v := (θ + z.re) / 2
    have hθv : θ < v := by dsimp [v]; linarith
    have hvz : v < z.re := by dsimp [v]; linarith
    exact (hprefix z).add (complexMellinOn_tail_analyticOnNhd (adjustedPrimeError C θ)
      a v ha (measurable_adjustedPrimeError C θ) (htail v hθv) z hvz)
  exact riemannZeta_ne_zero_of_analytic_mellin_formula C θ hθ0 hθ.le F hF hinit ρ hρ

#print axioms regularizedZeta_eventually_ne_zero
#print axioms negative_real_pole_tendsto_atBot
#print axioms adjustedPrimeError_abscissa_le
#print axioms adjustedPrimeError_tail_converges
#print axioms riemannZeta_ne_zero_of_oneSidedBound
end RiemannResearch

namespace RiemannResearch

/-- The functional equation carries any nontrivial zero to the left of the
critical line to a zero on its right. The cosine factor can vanish only
at an excluded zero of this form on the left. -/
theorem riemannZeta_reflect_left_zero (ρ : ℂ) (hρ : ρ.re < 1 / 2)
    (hz : riemannZeta ρ = 0) (htrivial : ¬ ∃ n : ℕ, ρ = -2 * (n + 1)) :
    riemannZeta (1 - ρ) = 0 := by
  let w : ℂ := 1 - ρ
  have hwpos : 0 < w.re := by
    simp only [w, Complex.sub_re, Complex.one_re]
    linarith
  have hwneg (n : ℕ) : w ≠ -(n : ℂ) := by
    intro he
    rw [he, Complex.neg_re, Complex.natCast_re] at hwpos
    exact (not_lt_of_ge (neg_nonpos.mpr (Nat.cast_nonneg n))) hwpos
  have hw1 : w ≠ 1 := by
    intro he
    have h0 : ρ = 0 := by dsimp [w] at he; linear_combination -he
    rw [h0, riemannZeta_zero] at hz
    norm_num at hz
  have hcos : Complex.cos (Real.pi * w / 2) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hwk : w = 2 * (k : ℂ) + 1 := by
      apply mul_left_cancel₀ hπ
      linear_combination 2 * hk
    have hρk : ρ = -2 * (k : ℂ) := by
      dsimp [w] at hwk
      linear_combination -hwk
    have hkr := congrArg Complex.re hwk
    simp [Complex.mul_re, Complex.add_re] at hkr
    have hk0 : 0 ≤ k := by
      by_contra! h
      have hkneg : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      linarith
    lift k to ℕ using hk0 with n
    cases n with
    | zero =>
        rw [show ρ = 0 by simpa using hρk, riemannZeta_zero] at hz
        norm_num at hz
    | succ n =>
        exact htrivial ⟨n, by simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_succ] using hρk⟩
  have hbase : (2 : ℂ) * Real.pi ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hfactor : 2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
      Complex.cos (Real.pi * w / 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr
      (Or.inl hbase))) (Complex.Gamma_ne_zero_of_re_pos hwpos)) hcos
  have hback : 1 - w = ρ := by dsimp [w]; ring
  have hfunc := riemannZeta_one_sub hwneg hw1
  rw [hback, hz] at hfunc
  exact (mul_eq_zero.mp hfunc.symm).resolve_left hfactor

/-- A zero-free right half-plane implies the exact Mathlib proposition
after reflecting potentially left-hand nontrivial zeros. -/
theorem riemannHypothesis_of_right_zero_free
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro ρ hz htriv _
  apply le_antisymm
  · exact le_of_not_gt (fun h => hfree ρ h hz)
  · by_contra! h
    have hright : 1 / 2 < (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact hfree _ hright (riemannZeta_reflect_left_zero ρ h hz htriv)

/-- The family of one-sided prime-error bounds for exponents strictly
between one half and one implies Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_oneSidedBounds
    (h : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → OneSidedBound θ) : RiemannHypothesis := by
  apply riemannHypothesis_of_right_zero_free
  intro z hz
  obtain ⟨θ, hhalf, hmin⟩ := exists_between
    (show (1 / 2 : ℝ) < min (1 : ℝ) z.re from lt_min (by norm_num) hz)
  have hθ1 := hmin.trans_le (min_le_left _ _)
  exact riemannZeta_ne_zero_of_oneSidedBound θ (by linarith) hθ1
    (h θ hhalf hθ1) z (hmin.trans_le (min_le_right _ _))

#print axioms riemannZeta_reflect_left_zero
#print axioms riemannHypothesis_of_right_zero_free
#print axioms riemannHypothesis_of_oneSidedBounds
end RiemannResearch

namespace RiemannResearch
open MeasureTheory Filter Set Asymptotics

/-- The unadjusted prime-error transform on its initial half-plane. -/
theorem primeError_mellin_eq_zeta (z : ℂ) (hz : 1 < z.re) :
    complexMellinOn primeError (Ici 0) z =
      1 / (z - 1) + (deriv riemannZeta z / riemannZeta z) / z := by
  have h := (adjustedPrimeError_mellin 0 0 z zero_le_one hz).2
  simp only [zero_mul, zero_sub, Complex.ofReal_neg, neg_mul, integral_neg,
    Complex.ofReal_zero, zero_div] at h
  unfold complexMellinOn
  simp only [neg_mul]
  linear_combination -h

/-- Mathlib's RH excludes every zero strictly to the right of the critical line. -/
theorem riemannZeta_ne_zero_right_of_riemannHypothesis (h : RiemannHypothesis)
    (z : ℂ) (hz : 1 / 2 < z.re) : riemannZeta z ≠ 0 := by
  intro hzero
  have hz1 : z ≠ 1 := fun h => riemannZeta_ne_zero_of_one_le_re (by simp [h]) hzero
  have hn : ¬ ∃ n : ℕ, z = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    norm_num [Complex.mul_re, Complex.add_re] at hz
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact hz.ne' (h z hzero hn hz1)

/-- RH is equivalent to the existence of a holomorphic continuation of the
prime-error Mellin transform to Re z > 1/2. This concerns analytic
continuation of the transform. -/
theorem riemannHypothesis_iff_primeError_mellin_continuation :
    RiemannHypothesis ↔ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {z : ℂ | 1 / 2 < z.re} ∧
      ∀ z : ℂ, 1 < z.re → F z = complexMellinOn primeError (Ici 0) z := by
  constructor
  · intro h
    let F := fun z : ℂ => (1 + deriv regularizedZeta z / regularizedZeta z) / z
    refine ⟨F, ?_, ?_⟩
    · intro z hz
      have hz' : (1 / 2 : ℝ) < z.re := hz
      have hz0 := Complex.ne_zero_of_re_pos ((by norm_num : 0 < (1 / 2 : ℝ)).trans hz')
      have hU0 : regularizedZeta z ≠ 0 := by
        by_cases hz1 : z = 1
        · simp [hz1]
        · rw [(regularizedZeta_eventuallyEq z hz1).eq_of_nhds]
          exact mul_ne_zero (sub_ne_zero.mpr hz1)
            (riemannZeta_ne_zero_right_of_riemannHypothesis h z hz')
      have hU := regularizedZeta_analyticAt z
      exact (analyticAt_const.add (hU.deriv.div hU hU0)).div analyticAt_id hz0
    · intro z hz
      have hz0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hz)
      have hz1 : z ≠ 1 := fun he => by simp [he] at hz
      have hζ := riemannZeta_ne_zero_of_one_le_re hz.le
      have he := regularizedZeta_mellin_eq z hz0 hz1 hζ
      rw [primeError_mellin_eq_zeta z hz]
      dsimp [F]
      linear_combination -he
  · rintro ⟨F, hF, hinit⟩
    apply riemannHypothesis_of_right_zero_free
    intro z hz
    apply riemannZeta_ne_zero_of_analytic_mellin_formula 0 (1 / 2) (by norm_num) (by norm_num)
      (fun w => -F w) (fun w hw => (hF w hw).neg) _ z hz
    intro w hw
    change -F w = _
    rw [hinit w hw, primeError_mellin_eq_zeta w hw]
    simp only [Complex.ofReal_zero, zero_div]
    ring

/-- The von Koch error estimate suffices for every exponent strictly
greater than one half in the one-sided criterion. -/
theorem oneSidedBound_of_vonKoch_estimate (θ : ℝ) (hθ : 1 / 2 < θ)
    (h : primeError =O[atTop] fun x => x ^ (1 / 2 : ℝ) * Real.log x ^ 2) :
    OneSidedBound θ := by
  let ε := (θ - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlog := (isLittleO_log_rpow_atTop hε).isBigO
  have hlog₂ : (fun x : ℝ => Real.log x ^ 2) =O[atTop] fun x => (x ^ ε) * (x ^ ε) := by
    simpa only [pow_two] using hlog.mul hlog
  have hweight : (fun x : ℝ => x ^ (1 / 2 : ℝ) * Real.log x ^ 2) =O[atTop] fun x => x ^ θ := by
    refine ((isBigO_refl (fun x : ℝ => x ^ (1 / 2 : ℝ)) atTop).mul hlog₂).congr'
      EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    dsimp [ε]
    ring
  obtain ⟨C, hCpos, hC⟩ := (h.trans hweight).exists_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hC.bound
  refine ⟨C, max 1 x₀, hCpos.le, le_max_left _ _, ?_⟩
  intro x hx
  have hx₁ : 1 ≤ x := (le_max_left 1 x₀).trans hx
  have hh := hx₀ x ((le_max_right 1 x₀).trans hx)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx₁) _)] at hh
  exact (Real.le_norm_self _).trans hh

#print axioms riemannZeta_ne_zero_of_analytic_mellin_formula
#print axioms primeError_mellin_eq_zeta
#print axioms riemannZeta_ne_zero_right_of_riemannHypothesis
#print axioms riemannHypothesis_iff_primeError_mellin_continuation
#print axioms oneSidedBound_of_vonKoch_estimate
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Interval Topology

/-- The oscillatory factor of the Perron kernel on a vertical line. -/
noncomputable def perronOscillatoryKernel (c u t : ℝ) : ℂ :=
  Complex.exp (((u : ℂ) * Complex.I) * (t : ℂ)) / ((c : ℂ) + (t : ℂ) * Complex.I)

theorem continuous_perronOscillatoryKernel (c u : ℝ) (hc : 0 < c) :
    Continuous (perronOscillatoryKernel c u) := by
  unfold perronOscillatoryKernel
  have hden (t : ℝ) : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    exact hc.ne' (by simpa [Complex.mul_re] using congrArg Complex.re h)
  exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (((u : ℂ) * Complex.I) * (t : ℂ))).div
    (by fun_prop) hden

/-- Integration by parts gives a uniform tail bound for the oscillatory
Perron kernel between any two positive heights. -/
theorem perronOscillatoryKernel_tail_bound (c u a b : ℝ)
    (hc : 0 < c) (hu : u ≠ 0) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ t in a..b, perronOscillatoryKernel c u t‖ ≤ 2 / (|u| * a) := by
  let D (t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  let E (t : ℝ) : ℂ := Complex.exp (((u : ℂ) * Complex.I) * (t : ℂ))
  let K : ℂ := (u : ℂ) * Complex.I
  let U (t : ℝ) : ℂ := (D t)⁻¹
  let V (t : ℝ) : ℂ := E t / K
  let U' (t : ℝ) : ℂ := -Complex.I / (D t) ^ 2
  have hD (t : ℝ) : D t ≠ 0 := by
    intro h
    exact hc.ne' (by simpa [D, Complex.mul_re] using congrArg Complex.re h)
  have hK : K ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) Complex.I_ne_zero
  have hU (t : ℝ) : HasDerivAt U (U' t) t := by
    have h : HasDerivAt (fun z : ℂ => (c : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
      simpa only [id_eq, one_mul] using
        (((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (c : ℂ))
    exact (h.inv (hD t)).comp_ofReal
  have hV (t : ℝ) : HasDerivAt V (E t) t := by
    have h := ((((hasDerivAt_id (t : ℂ)).const_mul K).cexp).div_const K).comp_ofReal
    simpa only [V, E, K, id_eq, mul_one, mul_div_cancel_right₀ _ hK] using h
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun t => (hU t).continuousAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun t => (hV t).continuousAt
  have hU'c : Continuous U' := by
    exact continuous_const.div (by dsimp [D]; fun_prop) (fun t => pow_ne_zero _ (hD t))
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hby := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hUc.continuousOn hVc.continuousOn (fun t _ => hU t) (fun t _ => hV t)
      (hU'c.intervalIntegrable a b) (hEc.intervalIntegrable a b)
  have heq : (fun t => U t * E t) = perronOscillatoryKernel c u := by
    funext t
    simp only [U, D, E, perronOscillatoryKernel, div_eq_mul_inv]
    exact mul_comm _ _
  simp_rw [heq] at hby
  have hE (t : ℝ) : ‖E t‖ = 1 := by simp [E, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hVnorm (t : ℝ) : ‖V t‖ = |u|⁻¹ := by
    simp [V, norm_div, hE, K, Real.norm_eq_abs, one_div]
  have hDnorm (t : ℝ) (ht : 0 ≤ t) : t ≤ ‖D t‖ := by
    simpa [D, Complex.mul_im, abs_of_nonneg ht] using Complex.abs_im_le_norm (D t)
  have hend (t : ℝ) (ht : 0 < t) : ‖U t * V t‖ ≤ t⁻¹ * |u|⁻¹ := by
    rw [norm_mul, hVnorm]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (abs_nonneg u))
    simp only [U, norm_inv]
    exact inv_anti₀ ht (hDnorm t ht.le)
  have hrem (t : ℝ) (ht : t ∈ Icc a b) : ‖U' t * V t‖ ≤ t ^ (-2 : ℤ) * |u|⁻¹ := by
    have ht0 := ha.trans_le ht.1
    simp only [norm_mul, hVnorm, U', norm_div, norm_neg, Complex.norm_I, norm_pow, one_div, zpow_neg,
      zpow_ofNat]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (abs_nonneg u))
    exact inv_anti₀ (pow_pos ht0 _) (pow_le_pow_left₀ ht0.le (hDnorm t ht0.le) _)
  have hnot : (0 : ℝ) ∉ [[a, b]] := by
    rw [uIcc_of_le hab]
    exact fun hh => (not_le_of_gt ha) hh.1
  have hmono := intervalIntegral.integral_mono_on hab
    ((hU'c.mul hVc).norm.intervalIntegrable a b)
    ((intervalIntegral.intervalIntegrable_zpow (μ := volume) (n := -2) (Or.inr hnot)).mul_const (|u|⁻¹)) hrem
  have hcalc : (∫ t in a..b, t ^ (-2 : ℤ) * |u|⁻¹) =
      (a⁻¹ - b⁻¹) * |u|⁻¹ := by
    rw [intervalIntegral.integral_mul_const, integral_zpow (Or.inr ⟨by norm_num, hnot⟩)]
    norm_num [zpow_neg]
    ring_nf
    simp
  rw [hby]
  calc
    _ ≤ ‖U b * V b‖ + ‖U a * V a‖ + ‖∫ t in a..b, U' t * V t‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ b⁻¹ * |u|⁻¹ + a⁻¹ * |u|⁻¹ + (a⁻¹ - b⁻¹) * |u|⁻¹ := by
      apply add_le_add (add_le_add (hend b (ha.trans_le hab)) (hend a ha))
      exact (intervalIntegral.norm_integral_le_integral_norm hab).trans (hmono.trans_eq hcalc)
    _ = _ := by rw [div_eq_mul_inv, mul_inv_rev]; ring

/-- The positive-height integral of the oscillatory Perron kernel
converges as an improper limit for a nonzero frequency. -/
theorem perronOscillatoryKernel_tendsto_pos (c u : ℝ) (hc : 0 < c) (hu : u ≠ 0) :
    ∃ L : ℂ, Tendsto (fun b : ℝ => ∫ t in (0 : ℝ)..b, perronOscillatoryKernel c u t)
      atTop (𝓝 L) := by
  apply CompleteSpace.complete
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have hu0 : 0 < |u| := abs_pos.mpr hu
  let N := max 1 (3 / (|u| * ε))
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  have hsmall : 2 / (|u| * N) < ε := by
    apply (div_lt_iff₀ (mul_pos hu0 hN)).mpr
    calc
      2 < 3 := by norm_num
      _ ≤ N * (|u| * ε) := (div_le_iff₀ (mul_pos hu0 hε)).mp (le_max_right _ _)
      _ = ε * (|u| * N) := by ring
  refine ⟨N, fun b hb => ?_⟩
  have hcont := continuous_perronOscillatoryKernel c u hc
  rw [dist_eq_norm, ← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 N) (hcont.intervalIntegrable N b), add_sub_cancel_left]
  exact (perronOscillatoryKernel_tail_bound c u N b hc hu hN hb).trans_lt hsmall

/-- For x > 0, factoring out the positive real power leaves oscillation
with frequency log x. -/
theorem perron_kernel_eq_factor (x c t : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I) =
      (x ^ c : ℝ) * perronOscillatoryKernel c (Real.log x) t := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [perronOscillatoryKernel, Complex.ofReal_cpow hx.le, ← mul_div_assoc]
  simp only [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 2
  ring

/-- The vertical-line Perron kernel has an explicit truncation bound away
from the threshold x = 1. -/
theorem perron_kernel_tail_bound (x c a b : ℝ) (hx : 0 < x) (hx1 : x ≠ 1)
    (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ t in a..b, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (x ^ c : ℝ) * (2 / (|Real.log x| * a)) := by
  simp_rw [perron_kernel_eq_factor x c _ hx, intervalIntegral.integral_const_mul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
  have hlog : Real.log x ≠ 0 := by
    intro he
    exact hx1 ((Real.exp_log hx).symm.trans (by simp [he]))
  exact mul_le_mul_of_nonneg_left
    (perronOscillatoryKernel_tail_bound c (Real.log x) a b hc hlog ha hab) (Real.rpow_nonneg hx.le _)

/-- The two halves of a symmetric vertical truncation are conjugate. -/
theorem perronOscillatoryKernel_integral_symm (c u b : ℝ) (hc : 0 < c) :
    (∫ t in -b..b, perronOscillatoryKernel c u t) =
      (starRingEnd ℂ) (∫ t in (0 : ℝ)..b, perronOscillatoryKernel c u t) +
        ∫ t in (0 : ℝ)..b, perronOscillatoryKernel c u t := by
  have hsym (t : ℝ) :
      perronOscillatoryKernel c u (-t) = (starRingEnd ℂ) (perronOscillatoryKernel c u t) := by
    simp only [perronOscillatoryKernel, Complex.ofReal_neg, map_div₀, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_conj, neg_mul, mul_neg]
  have hcont := continuous_perronOscillatoryKernel c u hc
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-b) 0) (hcont.intervalIntegrable 0 b)]
  congr 1
  have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := b)
    (f := perronOscillatoryKernel c u)
  simp only [neg_zero] at hneg
  rw [← hneg]
  simp only [hsym, intervalIntegral, integral_conj, map_sub]

/-- Conjugate symmetry turns the positive-height limit into the
symmetric vertical-line limit used in Perron's formula. -/
theorem perronOscillatoryKernel_tendsto_symmetric (c u : ℝ) (hc : 0 < c) (hu : u ≠ 0) :
    ∃ L : ℂ, Tendsto (fun b : ℝ => ∫ t in -b..b, perronOscillatoryKernel c u t)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := perronOscillatoryKernel_tendsto_pos c u hc hu
  refine ⟨(starRingEnd ℂ) L + L, ?_⟩
  have hconj : Continuous (starRingEnd ℂ : ℂ → ℂ) := Complex.continuous_conj
  exact ((hconj.continuousAt.tendsto.comp hL).add hL).congr
    (fun b => (perronOscillatoryKernel_integral_symm c u b hc).symm)

/-- The symmetric improper vertical-line Perron integral exists for
positive x away from the step threshold. -/
theorem perron_kernel_tendsto_symmetric (x c : ℝ)
    (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c) :
    ∃ L : ℂ, Tendsto (fun b : ℝ => ∫ t in -b..b,
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 L) := by
  have hlog : Real.log x ≠ 0 := by
    intro he
    exact hx1 ((Real.exp_log hx).symm.trans (by simp [he]))
  obtain ⟨L, hL⟩ := perronOscillatoryKernel_tendsto_symmetric c (Real.log x) hc hlog
  refine ⟨(x ^ c : ℝ) * L, ?_⟩
  simp_rw [perron_kernel_eq_factor x c _ hx, intervalIntegral.integral_const_mul]
  exact hL.const_mul _

#print axioms continuous_perronOscillatoryKernel
#print axioms perronOscillatoryKernel_tail_bound
#print axioms perronOscillatoryKernel_tendsto_pos
#print axioms perron_kernel_eq_factor
#print axioms perron_kernel_tail_bound
#print axioms perronOscillatoryKernel_tendsto_symmetric
#print axioms perron_kernel_tendsto_symmetric
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Interval Topology ComplexConjugate

/-- A rectangular contour identifies two vertical limits once the two
horizontal integrals tend to zero. -/
theorem vertical_integral_limits_eq (f : ℂ → ℂ) (a b : ℝ) (A B : ℂ)
    (hf : ∀ z : ℂ, z.re ∈ [[a, b]] → DifferentiableAt ℂ f z)
    (ha : Tendsto (fun T : ℝ => ∫ t in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 A))
    (hb : Tendsto (fun T : ℝ => ∫ t in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 B))
    (hlo : Tendsto (fun T : ℝ => ∫ t in a..b, f ((t : ℂ) + (-(T : ℂ)) * Complex.I)) atTop (𝓝 0))
    (hhi : Tendsto (fun T : ℝ => ∫ t in a..b, f ((t : ℂ) + (T : ℂ) * Complex.I)) atTop (𝓝 0)) :
    A = B := by
  have heq (T : ℝ) : Complex.I *
      ((∫ t in -T..T, f ((b : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t in -T..T, f ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t in a..b, f ((t : ℂ) + (T : ℂ) * Complex.I)) -
        ∫ t in a..b, f ((t : ℂ) + (-(T : ℂ)) * Complex.I) := by
    let z : ℂ := (a : ℂ) - (T : ℂ) * Complex.I
    let w : ℂ := (b : ℂ) + (T : ℂ) * Complex.I
    have hzre : z.re = a := by simp [z, Complex.mul_re]
    have hwre : w.re = b := by simp [w, Complex.mul_re]
    have hzim : z.im = -T := by simp [z, Complex.mul_im]
    have hwim : w.im = T := by simp [w, Complex.mul_im]
    have hd : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
      intro v hv
      apply (hf v ?_).differentiableWithinAt
      simpa only [← hzre, ← hwre] using hv.1
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hd
    simp only [hzre, hwre, hzim, hwim, Complex.ofReal_neg, smul_eq_mul] at hrect
    linear_combination hrect
  have hV := (hb.sub ha).const_mul Complex.I
  have hH := (hhi.sub hlo).congr (fun T => (heq T).symm)
  have h := tendsto_nhds_unique hV hH
  exact (sub_eq_zero.mp ((mul_eq_zero.mp (h.trans (sub_self _))).resolve_left Complex.I_ne_zero)).symm

/-- On fixed horizontal segments, the Perron integrand tends to zero
after integration as the absolute height goes to infinity. -/
theorem perron_horizontal_tendsto_zero (u a b k : ℝ) (hk : |k| = 1) :
    Tendsto (fun T : ℝ => ∫ t in a..b,
      Complex.exp ((u : ℂ) * ((t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I)) /
        ((t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  let M := Real.exp (|u| * (|a| + |b|))
  have hmajor : Tendsto (fun T : ℝ => (M * |b - a|) * T⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).const_mul
      (M * |b - a|)
  refine squeeze_zero_norm' ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simp only [← div_eq_mul_inv]
    calc
      _ ≤ (M / T) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        have ht' : t ∈ [[a, b]] := uIoc_subset_uIcc ht
        have htb : |t| ≤ |a| + |b| := by
          apply abs_le.mpr
          constructor
          · refine (le_min ?_ ?_).trans ht'.1
            · linarith [neg_abs_le a, abs_nonneg b]
            · linarith [neg_abs_le b, abs_nonneg a]
          · refine ht'.2.trans (max_le ?_ ?_)
            · linarith [le_abs_self a, abs_nonneg b]
            · linarith [le_abs_self b, abs_nonneg a]
        have hnum : Real.exp (u * t) ≤ M := by
          apply Real.exp_le_exp.mpr
          refine (le_abs_self (u * t)).trans ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left htb (abs_nonneg u)
        have hden : T ≤ ‖(t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I‖ := by
          simpa [Complex.mul_im, abs_mul, hk, abs_of_pos hT] using
            Complex.abs_im_le_norm ((t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I)
        rw [norm_div, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact (div_le_div_of_nonneg_left (Real.exp_pos _).le hT hden).trans
          (div_le_div_of_nonneg_right hnum hT.le)
      _ = (M * |b - a|) / T := by ring

/-- Factoring the real part of the exponential gives the ordinary
oscillatory Perron kernel on any vertical line. -/
theorem perron_exp_vertical_eq (u c t : ℝ) :
    Complex.exp ((u : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
      ((c : ℂ) + (t : ℂ) * Complex.I) =
      (Real.exp (u * c) : ℂ) * perronOscillatoryKernel c u t := by
  unfold perronOscillatoryKernel
  rw [Complex.ofReal_exp, Complex.ofReal_mul, ← mul_div_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- A bound uniform in the location of a vertical line with real part at least one. -/
theorem perronOscillatoryKernel_limit_bound (c u : ℝ) (hc : 1 ≤ c) (hu : u ≠ 0) (L : ℂ)
    (hL : Tendsto (fun T : ℝ => ∫ t in -T..T, perronOscillatoryKernel c u t) atTop (𝓝 L)) :
    ‖L‖ ≤ 2 * (1 + 2 / |u|) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hcont := continuous_perronOscillatoryKernel c u hc0
  apply le_of_tendsto hL.norm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hfirst : ‖∫ t in (0 : ℝ)..1, perronOscillatoryKernel c u t‖ ≤ 1 := by
    simpa using (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      (a := (0 : ℝ)) (b := 1) (f := perronOscillatoryKernel c u) (fun t _ => by
        have hden : c ≤ ‖(c : ℂ) + (t : ℂ) * Complex.I‖ := by
          simpa [Complex.mul_re] using Complex.re_le_norm ((c : ℂ) + (t : ℂ) * Complex.I)
        rw [perronOscillatoryKernel, norm_div, Complex.norm_exp]
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, zero_sub, neg_zero, sub_zero,
          Real.exp_zero]
        exact (div_le_iff₀ (hc0.trans_le hden)).mpr (by simpa using hc.trans hden)))
  have hpos : ‖∫ t in (0 : ℝ)..T, perronOscillatoryKernel c u t‖ ≤ 1 + 2 / |u| := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 1)
      (hcont.intervalIntegrable 1 T)]
    have htail := perronOscillatoryKernel_tail_bound c u 1 T hc0 hu zero_lt_one hT
    rw [mul_one] at htail
    exact (norm_add_le _ _).trans (add_le_add hfirst htail)
  rw [perronOscillatoryKernel_integral_symm c u T hc0]
  apply (norm_add_le _ _).trans
  rw [RCLike.norm_conj]
  linarith

/-- Below the jump, the symmetric vertical-line Perron integral has limit zero. -/
theorem perron_exp_vertical_tendsto_zero_of_neg (u c : ℝ) (hu : u < 0) (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      Complex.exp ((u : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
        ((c : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 0) := by
  let f : ℂ → ℂ := fun z => Complex.exp ((u : ℂ) * z) / z
  obtain ⟨L, hL⟩ := perronOscillatoryKernel_tendsto_symmetric c u hc hu.ne
  have hV (d : ℝ) (A : ℂ)
      (hA : Tendsto (fun T : ℝ => ∫ t in -T..T, perronOscillatoryKernel d u t) atTop (𝓝 A)) :
      Tendsto (fun T : ℝ => ∫ t in -T..T, f ((d : ℂ) + (t : ℂ) * Complex.I))
        atTop (𝓝 ((Real.exp (u * d) : ℂ) * A)) := by
    simp_rw [f, perron_exp_vertical_eq, intervalIntegral.integral_const_mul]
    exact hA.const_mul _
  have hbound : ∀ᶠ d : ℝ in atTop,
      ‖(Real.exp (u * c) : ℂ) * L‖ ≤ Real.exp (u * d) * (2 * (1 + 2 / |u|)) := by
    filter_upwards [eventually_ge_atTop (max c 1)] with d hd
    have hcd : c ≤ d := (le_max_left _ _).trans hd
    have hd1 : 1 ≤ d := (le_max_right _ _).trans hd
    obtain ⟨B, hB⟩ := perronOscillatoryKernel_tendsto_symmetric d u
      (zero_lt_one.trans_le hd1) hu.ne
    have heq := vertical_integral_limits_eq f c d _ _ ?_ (hV c L hL) (hV d B hB)
      (by simpa [f] using perron_horizontal_tendsto_zero u c d (-1) (by norm_num))
      (by simpa [f] using perron_horizontal_tendsto_zero u c d 1 (by norm_num))
    · rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (perronOscillatoryKernel_limit_bound d u hd1 hu.ne B hB)
        (Real.exp_pos _).le
    · intro z hz
      rw [uIcc_of_le hcd] at hz
      have hr : 0 < z.re := hc.trans_le hz.1
      exact (show DifferentiableAt ℂ (fun z : ℂ => Complex.exp ((u : ℂ) * z)) z by fun_prop).div
        differentiableAt_id (Complex.ne_zero_of_re_pos hr)
  have hdecay : Tendsto (fun d : ℝ => Real.exp (u * d) * (2 * (1 + 2 / |u|))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (Tendsto.const_mul_atTop_of_neg hu (tendsto_id : Tendsto (fun d : ℝ => d) atTop atTop))
    simpa using h.mul_const (2 * (1 + 2 / |u|))
  have hz : (Real.exp (u * c) : ℂ) * L = 0 :=
    norm_le_zero_iff.mp (ge_of_tendsto hdecay hbound)
  simpa only [f, hz] using hV c L hL

/-- The symmetric kernel at zero frequency has an exact finite-height value. -/
theorem perronOscillatoryKernel_integral_zero (c T : ℝ) (hc : 0 < c) :
    (∫ t in -T..T, perronOscillatoryKernel c 0 t) =
      ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
  have hcont := continuous_perronOscillatoryKernel c 0 hc
  have hreal (T : ℝ) :
      (∫ t in (0 : ℝ)..T, perronOscillatoryKernel c 0 t).re = Real.arctan (T / c) := by
    have hlin := Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := volume) 0 T)
    change (∫ t in (0 : ℝ)..T, (perronOscillatoryKernel c 0 t).re) =
      (∫ t in (0 : ℝ)..T, perronOscillatoryKernel c 0 t).re at hlin
    rw [← hlin]
    have hre (t : ℝ) : (perronOscillatoryKernel c 0 t).re = c⁻¹ * (1 + (t / c) ^ 2)⁻¹ := by
      simp only [perronOscillatoryKernel, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_div,
        Complex.inv_re, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, zero_add, add_zero, mul_one, ← pow_two]
      field_simp [hc.ne', show c ^ 2 + t ^ 2 ≠ 0 by positivity,
        show 1 + (t / c) ^ 2 ≠ 0 by positivity]
      ring
    simp_rw [hre, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) hc.ne']
    simp [smul_eq_mul, hc.ne', integral_inv_one_add_sq]
  rw [perronOscillatoryKernel_integral_symm c 0 T hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, hreal, Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, Complex.ofReal_im, neg_add_cancel]

/-- At the jump, the symmetric Perron integral is π before normalization. -/
theorem perron_exp_vertical_tendsto_at_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      Complex.exp ((0 : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
        ((c : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 (Real.pi : ℂ)) := by
  have hlim : Tendsto (fun T : ℝ => Real.arctan (T / c)) atTop (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      (tendsto_id.atTop_div_const hc)
  simp_rw [zero_mul, Complex.exp_zero]
  have hnorm (t : ℝ) : 1 / ((c : ℂ) + (t : ℂ) * Complex.I) = perronOscillatoryKernel c 0 t := by
    simp [perronOscillatoryKernel]
  simp_rw [hnorm, fun T => perronOscillatoryKernel_integral_zero c T hc]
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim.const_mul (2 : ℝ))
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring] at h
  exact h

/-- Reflecting a vertical line reverses both the frequency and the sign
of the unnormalized Perron integral. -/
theorem perron_exp_vertical_reflect (u c T : ℝ) :
    (∫ t in -T..T, Complex.exp ((u : ℂ) * (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
      (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
    -(∫ t in -T..T, Complex.exp (((-u : ℝ) : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
      ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((u : ℂ) * (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
    (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs := intervalIntegral.integral_comp_neg (a := -T) (b := T) (f := f)
  simp only [neg_neg] at hs
  change (∫ t in -T..T, f t) = _
  rw [← hs, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  have hden : (((-c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) =
      -((c : ℂ) + (t : ℂ) * Complex.I) := by push_cast; ring
  dsimp only [f]
  rw [hden]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, div_neg]

/-- Above the jump, subtract the pole at zero and shift the remaining
entire integrand across the imaginary axis. -/
theorem perron_exp_vertical_tendsto_of_pos (u c : ℝ) (hu : 0 < u) (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      Complex.exp ((u : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
        ((c : ℂ) + (t : ℂ) * Complex.I)) atTop (𝓝 (2 * (Real.pi : ℂ))) := by
  let E (v : ℝ) (z : ℂ) := Complex.exp ((v : ℂ) * z) / z
  let f := dslope (fun z : ℂ => Complex.exp ((u : ℂ) * z)) 0
  have hdiff (z : ℂ) : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((u : ℂ) * w)) z := by
    fun_prop
  have hf (z : ℂ) : DifferentiableAt ℂ f z := by
    by_cases hz : z = 0
    · subst z
      apply AnalyticAt.differentiableAt
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact (differentiableAt_dslope_of_ne hw).mpr (hdiff w)
      · exact continuousAt_dslope_same.mpr (hdiff 0)
    · exact (differentiableAt_dslope_of_ne hz).mpr (hdiff z)
  have hE (z : ℂ) (hz : z ≠ 0) : f z = E u z - E 0 z := by
    simp only [f, dslope_of_ne _ hz, slope_def_field, E, mul_zero, sub_zero, Complex.exp_zero,
      Complex.ofReal_zero, zero_mul, sub_div]
  have hInt (g : ℝ → ℂ) (hg : Continuous g) (hn : ∀ t, g t ≠ 0) (a b : ℝ) :
      (∫ t in a..b, f (g t)) = (∫ t in a..b, E u (g t)) - ∫ t in a..b, E 0 (g t) := by
    have hEc (v : ℝ) : Continuous (fun t => E v (g t)) :=
      ((Complex.continuous_exp.comp (continuous_const.mul hg)).div hg hn)
    simp_rw [hE _ (hn _)]
    exact intervalIntegral.integral_sub ((hEc u).intervalIntegrable a b)
      ((hEc 0).intervalIntegrable a b)
  have hline (d : ℝ) (hd : d ≠ 0) (T : ℝ) :
      (∫ t in -T..T, f ((d : ℂ) + (t : ℂ) * Complex.I)) =
        (∫ t in -T..T, E u ((d : ℂ) + (t : ℂ) * Complex.I)) -
        ∫ t in -T..T, E 0 ((d : ℂ) + (t : ℂ) * Complex.I) :=
    hInt _ (by fun_prop) (fun t hz => hd (by simpa [Complex.mul_re] using congrArg Complex.re hz)) _ _
  have hhorizontal (k : ℝ) (hk : |k| = 1) :
      Tendsto (fun T : ℝ => ∫ t in -c..c, f ((t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by
    have hlim := (perron_horizontal_tendsto_zero u (-c) c k hk).sub
      (perron_horizontal_tendsto_zero 0 (-c) c k hk)
    rw [sub_self] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hk0 : k ≠ 0 := by intro hzero; simp [hzero] at hk
    have heq := hInt (fun t : ℝ => (t : ℂ) + ((k * T : ℝ) : ℂ) * Complex.I) (by fun_prop)
      (fun t hz => (mul_ne_zero hk0 hT.ne') (by simpa [Complex.mul_im] using congrArg Complex.im hz))
      (-c) c
    exact heq.symm
  have hleft (v : ℝ) (A : ℂ)
      (hA : Tendsto (fun T : ℝ => ∫ t in -T..T, E (-v) ((c : ℂ) + (t : ℂ) * Complex.I))
        atTop (𝓝 A)) :
      Tendsto (fun T : ℝ => ∫ t in -T..T, E v (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        atTop (𝓝 (-A)) :=
    hA.neg.congr (fun T => (perron_exp_vertical_reflect v c T).symm)
  have hzero : Tendsto (fun T : ℝ => ∫ t in -T..T, E 0 ((c : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 (Real.pi : ℂ)) := perron_exp_vertical_tendsto_at_zero c hc
  have hL0 := hleft u 0 (perron_exp_vertical_tendsto_zero_of_neg (-u) c (neg_lt_zero.mpr hu) hc)
  have hLπ := hleft 0 (Real.pi : ℂ) (by simpa only [neg_zero] using hzero)
  have hLf : Tendsto (fun T : ℝ => ∫ t in -T..T, f (((-c : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 (Real.pi : ℂ)) := by
    have h := (hL0.sub hLπ).congr (fun T => (hline (-c) (neg_ne_zero.mpr hc.ne') T).symm)
    simpa only [neg_zero, zero_sub, neg_neg] using h
  obtain ⟨L, hL⟩ := perronOscillatoryKernel_tendsto_symmetric c u hc hu.ne'
  have hR : Tendsto (fun T : ℝ => ∫ t in -T..T, E u ((c : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 ((Real.exp (u * c) : ℂ) * L)) := by
    simp_rw [E, perron_exp_vertical_eq, intervalIntegral.integral_const_mul]
    exact hL.const_mul _
  have hRf := (hR.sub hzero).congr (fun T => (hline c hc.ne' T).symm)
  have heq := vertical_integral_limits_eq f (-c) c _ _ (fun z _ => hf z)
    hLf hRf
    (by simpa only [neg_mul, one_mul, Complex.ofReal_neg] using hhorizontal (-1) (by norm_num))
    (by simpa only [one_mul] using hhorizontal 1 (by norm_num))
  have hvalue : (Real.exp (u * c) : ℂ) * L = 2 * (Real.pi : ℂ) := by
    linear_combination -heq
  simpa only [E, hvalue] using hR

/-- The exact symmetric Perron limit, before division by 2π. -/
theorem perron_kernel_tendsto_step (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Tendsto (fun T : ℝ => ∫ t in -T..T,
      (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I))
      atTop (𝓝 (if x < 1 then 0 else if x = 1 then (Real.pi : ℂ) else 2 * (Real.pi : ℂ))) := by
  have heq (T : ℝ) : (∫ t in -T..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t in -T..T, Complex.exp ((Real.log x : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) /
        ((c : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
  simp_rw [heq]
  rcases lt_trichotomy x 1 with h | rfl | h
  · simpa only [if_pos h] using perron_exp_vertical_tendsto_zero_of_neg (Real.log x) c
      (Real.log_neg hx h) hc
  · simp only [lt_irrefl, if_false, if_true, Real.log_one, Complex.ofReal_zero]
    exact perron_exp_vertical_tendsto_at_zero c hc
  · simpa only [if_neg (not_lt_of_gt h), if_neg h.ne'] using
      perron_exp_vertical_tendsto_of_pos (Real.log x) c (Real.log_pos h) hc

#print axioms vertical_integral_limits_eq
#print axioms perron_horizontal_tendsto_zero
#print axioms perron_exp_vertical_eq
#print axioms perronOscillatoryKernel_integral_symm
#print axioms perronOscillatoryKernel_limit_bound
#print axioms perron_exp_vertical_tendsto_zero_of_neg
#print axioms perronOscillatoryKernel_integral_zero
#print axioms perron_exp_vertical_tendsto_at_zero
#print axioms perron_exp_vertical_reflect
#print axioms perron_exp_vertical_tendsto_of_pos
#print axioms perron_kernel_tendsto_step
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Interval Topology

/-- The symmetric finite-height Perron integral, before normalization. -/
noncomputable def perronTruncatedKernel (x c T : ℝ) : ℂ :=
  ∫ t in -T..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
    ((c : ℂ) + (t : ℂ) * Complex.I)

/-- The unnormalized Perron step, taking its half value at the jump. -/
noncomputable def perronStep (x : ℝ) : ℂ :=
  if x < 1 then 0 else if x = 1 then (Real.pi : ℂ) else 2 * (Real.pi : ℂ)

/-- For an absolutely convergent Dirichlet series, the finite-height
integral can be taken term by term. The term of index zero is omitted. -/
theorem LSeries_perron_truncated (f : ℕ → ℂ) (x c T : ℝ)
    (hx : 0 < x) (hc : 0 < c) (hf : LSeriesSummable f (c : ℂ)) :
    (∫ t in -T..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I) * LSeries f ((c : ℂ) + (t : ℂ) * Complex.I)) =
    ∑' n : ℕ, if n = 0 then 0 else f n * perronTruncatedKernel (x / (n : ℝ)) c T := by
  let z (t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * Complex.I
  let K (y t : ℝ) : ℂ := (y : ℂ) ^ z t / z t
  have hzre (t : ℝ) : (z t).re = c := by simp [z, Complex.mul_re]
  have hKn (t : ℝ) : ‖K x t‖ ≤ x ^ c / c := by
    have hb : c ≤ ‖z t‖ := hzre t ▸ Complex.re_le_norm (z t)
    dsimp only [K]
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, hzre]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) hc hb
  have hKc (y : ℝ) (hy : 0 < y) : Continuous (K y) := by
    simp_rw [K, z, perron_kernel_eq_factor y c _ hy]
    exact continuous_const.mul (continuous_perronOscillatoryKernel c (Real.log y) hc)
  let F (n : ℕ) : C(ℝ, ℂ) :=
    ⟨fun t => if n = 0 then 0 else f n * K (x / (n : ℝ)) t, by
      split_ifs with hn
      · exact continuous_const
      · exact continuous_const.mul (hKc _ (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))))⟩
  have hcpow (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
      ((x / (n : ℝ) : ℝ) : ℂ) ^ z t * (n : ℂ) ^ z t = (x : ℂ) ^ z t := by
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [← Complex.ofReal_natCast, ← Complex.mul_cpow_ofReal_nonneg
      (div_nonneg hx.le hn'.le) hn'.le, ← Complex.ofReal_mul, div_mul_cancel₀ _ hn'.ne']
  have hF (n : ℕ) (t : ℝ) : F n t = K x t * LSeries.term f (z t) n := by
    by_cases hn : n = 0
    · simp [F, hn]
    · have hnc : (n : ℂ) ^ z t ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))
      have he := (eq_div_iff hnc).mpr (hcpow n hn t)
      change (if n = 0 then 0 else f n * K (x / (n : ℝ)) t) = _
      rw [if_neg hn, LSeries.term_of_ne_zero hn]
      dsimp only [K]
      rw [he]
      ring
  let I : TopologicalSpace.Compacts ℝ := ⟨uIcc (-T) T, isCompact_uIcc⟩
  have hmajor : Summable (fun n => ‖LSeries.term f (c : ℂ) n‖ * (x ^ c / c)) :=
    (summable_norm_iff.mpr hf).mul_right _
  have hsum : Summable (fun n => ‖(F n).restrict I‖) := by
    refine hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
    apply (ContinuousMap.norm_le ((F n).restrict I) (mul_nonneg (norm_nonneg _)
      (div_nonneg (Real.rpow_nonneg hx.le _) hc.le))).mpr
    intro t
    change ‖F n t‖ ≤ _
    rw [hF, norm_mul, mul_comm ‖K x t‖]
    have hn : ‖LSeries.term f (z t) n‖ = ‖LSeries.term f (c : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hzre, Complex.ofReal_re]
    rw [hn]
    exact mul_le_mul_of_nonneg_left (hKn t) (norm_nonneg _)
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (a := -T) (b := T) (f := F) hsum
  change (∫ t in -T..T, K x t * LSeries f (z t)) = _
  calc
    _ = ∫ t in -T..T, ∑' n : ℕ, F n t := by
      simp_rw [hF, tsum_mul_left, LSeries]
    _ = ∑' n : ℕ, ∫ t in -T..T, F n t := hswap.symm
    _ = _ := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · simp [F, hn]
      · simp [F, hn, K, z, perronTruncatedKernel, intervalIntegral.integral_const_mul]

/-- The truncated Perron integral of the negative logarithmic derivative
of zeta is the sum of the von Mangoldt weights times their kernels. -/
theorem vonMangoldt_perron_truncated (x c T : ℝ) (hx : 0 < x) (hc : 1 < c) :
    (∫ t in -T..T, (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
      ((c : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I))) =
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * perronTruncatedKernel (x / (n : ℝ)) c T := by
  have h := LSeries_perron_truncated (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    x c T hx (zero_lt_one.trans hc) (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa))
  have hL (t : ℝ) : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((c : ℂ) + (t : ℂ) * Complex.I) =
        -deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
          riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa [Complex.mul_re] using hc)
  simp_rw [hL] at h
  rw [h]
  apply tsum_congr
  intro n
  by_cases hn : n = 0 <;> simp [hn]

/-- The symmetric Perron truncation differs from the step by at most
twice the positive-height tail bound, away from the jump. -/
theorem perronTruncatedKernel_sub_step_bound (x c T : ℝ)
    (hx : 0 < x) (hx1 : x ≠ 1) (hc : 0 < c) (hT : 0 < T) :
    ‖perronTruncatedKernel x c T - perronStep x‖ ≤ (x ^ c : ℝ) * (4 / (|Real.log x| * T)) := by
  let u := Real.log x
  let P : ℝ → ℂ := fun b => ∫ t in (0 : ℝ)..b, perronOscillatoryKernel c u t
  have hu : u ≠ 0 := by
    intro he
    exact hx1 ((Real.exp_log hx).symm.trans (by simp [u, he]))
  have hscale (b : ℝ) : perronTruncatedKernel x c b =
      (x ^ c : ℝ) * ((starRingEnd ℂ) (P b) + P b) := by
    simp_rw [perronTruncatedKernel, perron_kernel_eq_factor x c _ hx, intervalIntegral.integral_const_mul]
    rw [perronOscillatoryKernel_integral_symm c u b hc]
  have hcont := continuous_perronOscillatoryKernel c u hc
  have hdiff (b : ℝ) (hb : T ≤ b) :
      ‖perronTruncatedKernel x c b - perronTruncatedKernel x c T‖ ≤
        (x ^ c : ℝ) * (4 / (|u| * T)) := by
    have hP : P b - P T = ∫ t in T..b, perronOscillatoryKernel c u t := by
      dsimp [P]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 T)
        (hcont.intervalIntegrable T b), add_sub_cancel_left]
    have heq : (starRingEnd ℂ) (P b) + P b - ((starRingEnd ℂ) (P T) + P T) =
        (starRingEnd ℂ) (P b - P T) + (P b - P T) := by
      rw [map_sub]
      ring
    rw [hscale, hscale, ← mul_sub, heq, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
    have hBd : ‖P b - P T‖ ≤ 2 / (|u| * T) := by
      rw [hP]
      exact perronOscillatoryKernel_tail_bound c u T b hc hu hT hb
    refine (norm_add_le _ _).trans ?_
    rw [RCLike.norm_conj]
    exact (add_le_add hBd hBd).trans_eq (by rw [← add_div]; norm_num)
  have hlim : Tendsto (perronTruncatedKernel x c) atTop (𝓝 (perronStep x)) :=
    perron_kernel_tendsto_step x c hx hc
  rw [norm_sub_rev]
  exact le_of_tendsto (hlim.sub tendsto_const_nhds).norm
    ((eventually_ge_atTop T).mono hdiff)

/-- When the Dirichlet index is at least twice the cutoff, the Perron
kernel obeys a bound with a fixed logarithmic denominator. -/
theorem perronTruncatedKernel_far_right_bound (x c T : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 2 * x ≤ (n : ℝ)) (hc : 0 < c) (hT : 0 < T) :
    ‖perronTruncatedKernel (x / (n : ℝ)) c T‖ ≤
      ((x / (n : ℝ)) ^ c : ℝ) * (4 / (Real.log 2 * T)) := by
  have hnpos : 0 < (n : ℝ) := by linarith
  let y := x / (n : ℝ)
  have hy : 0 < y := div_pos hx hnpos
  have hyhalf : y ≤ 1 / 2 := (div_le_iff₀ hnpos).mpr (by linarith)
  have hy1 : y < 1 := hyhalf.trans_lt (by norm_num)
  have hlog : Real.log 2 ≤ |Real.log y| := by
    have h := Real.log_le_log hy hyhalf
    rw [one_div, Real.log_inv] at h
    rw [abs_of_neg (Real.log_neg hy hy1)]
    linarith
  have hbound := perronTruncatedKernel_sub_step_bound y c T hy hy1.ne hc hT
  simp only [perronStep, if_pos hy1, sub_zero] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos (Real.log_pos (by norm_num)) hT)
      (mul_le_mul_of_nonneg_right hlog hT.le)) (Real.rpow_nonneg hy.le _))

#print axioms LSeries_perron_truncated
#print axioms vonMangoldt_perron_truncated
#print axioms perronTruncatedKernel_sub_step_bound
#print axioms perronTruncatedKernel_far_right_bound
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Interval Topology

/-- The jump contributes a half weight with a finite-height error at most 2c/T. -/
theorem perronTruncatedKernel_at_jump_bound (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖perronTruncatedKernel 1 c T - perronStep 1‖ ≤ 2 * c / T := by
  have heq : perronTruncatedKernel 1 c T = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
    simpa [perronTruncatedKernel, perronOscillatoryKernel] using
      perronOscillatoryKernel_integral_zero c T hc
  rw [heq, show perronStep 1 = (Real.pi : ℂ) by simp [perronStep],
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < T / c := div_pos hT hc
  have hi := Real.arctan_inv_of_pos hpos
  rw [inv_div] at hi
  have harctan (z : ℝ) (hz : 0 ≤ z) : Real.arctan z ≤ z := by
    rw [← sub_zero (Real.arctan z), ← Real.arctan_zero, ← integral_inv_one_add_sq]
    calc
      (∫ t in (0 : ℝ)..z, (1 + t ^ 2)⁻¹) ≤ ∫ _ in (0 : ℝ)..z, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hz
          ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => by positivity)
            |>.intervalIntegrable 0 z)
          (intervalIntegrable_const) (fun t _ => inv_le_one_of_one_le₀ (by linarith [sq_nonneg t]))
      _ = z := by simp
  have hn : 0 ≤ Real.arctan (c / T) := by
    simpa using Real.arctan_le_arctan (div_nonneg hc.le hT.le)
  rw [show 2 * Real.arctan (T / c) - Real.pi = -(2 * Real.arctan (c / T)) by linarith,
    abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hn)]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (harctan _ (div_nonneg hc.le hT.le)) (by norm_num)

/-- The logarithmic separation controls the relative distance on either side of the jump. -/
theorem div_max_le_abs_log_div (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (x / y)| := by
  rcases le_total x y with h | h
  · have hxy := (div_le_one hy).mpr h
    have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h),
      abs_of_nonpos (Real.log_nonpos (div_pos hx hy).le hxy)]
    rw [neg_sub, sub_div, div_self hy.ne']
    linarith
  · have hl := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hl
    rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h),
      Real.log_div hx.ne' hy.ne', abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy h)),
      sub_div, div_self hx.ne']
    linarith

/-- An explicit coefficient of 1/T for the weighted Perron error. The jump,
the nearby indices, and the infinite right tail have separate bounds. -/
noncomputable def perronSeriesErrorMajorant (f : ℕ → ℂ) (x c : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    if 2 * x ≤ (n : ℝ) then ‖LSeries.term f (c : ℂ) n‖ * (x ^ c * (4 / Real.log 2))
    else if x = (n : ℝ) then ‖f n‖ * (2 * c)
    else ‖f n‖ * ((x / (n : ℝ)) ^ c * (4 / (|x - n| / max x n)))

/-- The infinitely many tail coefficients are summable by absolute convergence
on the original vertical line. -/
theorem summable_perronSeriesErrorMajorant (f : ℕ → ℂ) (x c : ℝ) (hx : 0 < x)
    (hf : LSeriesSummable f (c : ℂ)) : Summable (perronSeriesErrorMajorant f x c) := by
  let N := ⌈2 * x⌉₊
  have hN : 2 * x ≤ (N : ℝ) := Nat.le_ceil _
  have hs := (summable_norm_iff.mpr hf).mul_right (x ^ c * (4 / Real.log 2))
  apply (summable_nat_add_iff N).mp
  apply ((summable_nat_add_iff N).mpr hs).congr
  intro k
  have hfar : 2 * x ≤ ((k + N : ℕ) : ℝ) :=
    hN.trans (Nat.cast_le.mpr (Nat.le_add_left _ _))
  have hn : k + N ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hfar
    linarith
  simp only [perronSeriesErrorMajorant, if_neg hn, if_pos hfar]

/-- The three coefficient bounds apply to every summand, including the jump. -/
theorem perronSeriesError_le_majorant (f : ℕ → ℂ) (x c T : ℝ) (n : ℕ)
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) :
    ‖(if n = 0 then 0 else f n *
      (perronTruncatedKernel (x / (n : ℝ)) c T - perronStep (x / (n : ℝ))))‖ ≤
      perronSeriesErrorMajorant f x c n / T := by
  by_cases hn : n = 0
  · simp [hn, perronSeriesErrorMajorant]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hy : 0 < x / (n : ℝ) := div_pos hx hnpos
  rw [if_neg hn, norm_mul, perronSeriesErrorMajorant, if_neg hn]
  split_ifs with hfar heq
  · have hlt : x / (n : ℝ) < 1 := (div_lt_one hnpos).mpr (by linarith)
    rw [perronStep, if_pos hlt, sub_zero]
    refine (mul_le_mul_of_nonneg_left
      (perronTruncatedKernel_far_right_bound x c T n hx hfar hc hT) (norm_nonneg _)).trans_eq ?_
    rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, Real.div_rpow hx.le hnpos.le]
    ring
  · have hdiv : x / (n : ℝ) = 1 := (div_eq_one_iff_eq hnpos.ne').mpr heq
    rw [hdiv, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (perronTruncatedKernel_at_jump_bound c T hc hT) (norm_nonneg _)
  · have hdiv : x / (n : ℝ) ≠ 1 := fun h => heq ((div_eq_one_iff_eq hnpos.ne').mp h)
    have hd : 0 < |x - (n : ℝ)| / max x (n : ℝ) :=
      div_pos (abs_pos.mpr (sub_ne_zero.mpr heq)) (lt_max_iff.mpr (Or.inl hx))
    have hgap := div_max_le_abs_log_div x n hx hnpos
    refine (mul_le_mul_of_nonneg_left (perronTruncatedKernel_sub_step_bound
      _ c T hy hdiv hc hT) (norm_nonneg _)).trans ?_
    calc
      _ ≤ ‖f n‖ * ((x / (n : ℝ)) ^ c * (4 / ((|x - n| / max x n) * T))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) (mul_pos hd hT)
            (mul_le_mul_of_nonneg_right hgap hT.le)) (Real.rpow_nonneg hy.le _)) (norm_nonneg _)
      _ = _ := by ring

/-- The finite-height series differs from its step sum by at most the
sum of the error coefficients divided by the height. -/
theorem perronSeries_sub_step_bound (f : ℕ → ℂ) (x c T : ℝ)
    (hx : 0 < x) (hc : 0 < c) (hT : 0 < T) (hf : LSeriesSummable f (c : ℂ)) :
    ‖(∑' n : ℕ, if n = 0 then 0 else f n * perronTruncatedKernel (x / (n : ℝ)) c T) -
      (∑' n : ℕ, if n = 0 then 0 else f n * perronStep (x / (n : ℝ)))‖ ≤
      (∑' n : ℕ, perronSeriesErrorMajorant f x c n) / T := by
  let A (n : ℕ) := if n = 0 then 0 else f n * perronTruncatedKernel (x / (n : ℝ)) c T
  let B (n : ℕ) := if n = 0 then 0 else f n * perronStep (x / (n : ℝ))
  have hB : Summable B := by
    apply summable_of_ne_finset_zero (s := Finset.range (⌊x⌋₊ + 1))
    intro n hn
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n :=
      Nat.cast_le.mpr (Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h)))
    have hxn : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by simpa using hcast)
    have hy : x / (n : ℝ) < 1 := (div_lt_one (hx.trans hxn)).mpr hxn
    simp [B, perronStep, hy]
  have hM := (summable_perronSeriesErrorMajorant f x c hx hf).hasSum.div_const T
  have hAB (n : ℕ) : ‖A n - B n‖ ≤ perronSeriesErrorMajorant f x c n / T := by
    by_cases hn : n = 0
    · simpa only [A, B, if_pos hn, sub_zero] using
        perronSeriesError_le_majorant f x c T n hx hc hT
    · simpa only [A, B, if_neg hn, ← mul_sub] using
        perronSeriesError_le_majorant f x c T n hx hc hT
  have hD := Summable.of_norm_bounded _ hM.summable hAB
  have hA : Summable A := by simpa only [sub_add_cancel] using hD.add hB
  change ‖(∑' n, A n) - (∑' n, B n)‖ ≤ _
  rw [← hA.tsum_sub hB]
  exact hD.hasSum.norm_le_of_bounded hM hAB

/-- In the Perron step sum, the last von Mangoldt weight is halved exactly
when the real cutoff is an integer. -/
theorem vonMangoldt_perron_step (x : ℝ) (hx : 0 < x) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * perronStep (x / (n : ℝ))) =
      2 * (Real.pi : ℂ) * (chebyshevPsi x : ℂ) -
        if x = (⌊x⌋₊ : ℝ) then (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : ℂ)
        else 0 := by
  rw [tsum_eq_sum (s := Finset.range (⌊x⌋₊ + 1))]
  · have hterm (n : ℕ) (hn : n ∈ Finset.range (⌊x⌋₊ + 1)) :
        (ArithmeticFunction.vonMangoldt n : ℂ) * perronStep (x / (n : ℝ)) =
          2 * (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) -
            if x = (⌊x⌋₊ : ℝ) ∧ n = ⌊x⌋₊ then
              (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
      by_cases hzero : n = 0
      · subst n
        simp
      have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)
      have hfloor : n ≤ ⌊x⌋₊ := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
      have hle : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hfloor
      have hnotlt : ¬ x / (n : ℝ) < 1 := not_lt.mpr ((one_le_div hnpos).mpr hle)
      have hiff : x / (n : ℝ) = 1 ↔ x = (⌊x⌋₊ : ℝ) ∧ n = ⌊x⌋₊ := by
        rw [div_eq_one_iff_eq hnpos.ne']
        constructor
        · intro he
          have hn' : n = ⌊x⌋₊ := by rw [he, Nat.floor_natCast]
          exact ⟨by rw [← hn', he], hn'⟩
        · rintro ⟨he, rfl⟩
          exact he
      simp only [perronStep, if_neg hnotlt, hiff]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [chebyshevPsi, Complex.ofReal_sum]
    by_cases he : x = (⌊x⌋₊ : ℝ)
    · simp only [if_pos he, and_iff_right he, Finset.sum_ite_eq', Finset.mem_range,
        Nat.lt_succ_self, if_true]
    · have hn (n : ℕ) : ¬ (x = (⌊x⌋₊ : ℝ) ∧ n = ⌊x⌋₊) := fun h => he h.1
      simp only [if_neg he, if_neg (hn _), Finset.sum_const_zero, sub_zero]
  · intro n hn
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ n :=
      Nat.cast_le.mpr (Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h)))
    have hxn : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le (by simpa using hcast)
    have hy : x / (n : ℝ) < 1 := (div_lt_one (hx.trans hxn)).mpr hxn
    simp [perronStep, hy]

/-- The zeta Perron integrand, before normalizing the contour integral. -/
noncomputable def zetaPerronIntegrand (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ z / z * (-deriv riemannZeta z / riemannZeta z)

/-- The unnormalized vertical zeta integral used in Perron inversion. -/
noncomputable def vonMangoldtPerronIntegral (x c T : ℝ) : ℂ :=
  ∫ t in -T..T, zetaPerronIntegrand x ((c : ℂ) + (t : ℂ) * Complex.I)

/-- The Chebyshev sum with half of the last weight removed at integers. -/
noncomputable def halfWeightedChebyshevPsi (x : ℝ) : ℝ :=
  chebyshevPsi x - if x = (⌊x⌋₊ : ℝ) then ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2 else 0

/-- For each positive cutoff, the truncated integral recovers the
half-weighted Chebyshev sum with an explicit error coefficient over T. -/
theorem vonMangoldtPerronIntegral_sub_psi_bound (x c T : ℝ)
    (hx : 0 < x) (hc : 1 < c) (hT : 0 < T) :
    ‖vonMangoldtPerronIntegral x c T - 2 * (Real.pi : ℂ) * (halfWeightedChebyshevPsi x : ℂ)‖ ≤
      (∑' n : ℕ, perronSeriesErrorMajorant (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        x c n) / T := by
  have h := perronSeries_sub_step_bound (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
    x c T hx (zero_lt_one.trans hc) hT
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa))
  have hzero (n : ℕ) (z : ℂ) :
      (if n = 0 then 0 else (ArithmeticFunction.vonMangoldt n : ℂ) * z) =
        (ArithmeticFunction.vonMangoldt n : ℂ) * z := by
    by_cases hn : n = 0 <;> simp [hn]
  simp_rw [hzero, ← vonMangoldt_perron_truncated x c T hx hc, vonMangoldt_perron_step x hx] at h
  unfold vonMangoldtPerronIntegral zetaPerronIntegrand
  convert h using 2
  unfold halfWeightedChebyshevPsi
  split_ifs <;> push_cast <;> ring

/-- Perron inversion converges to the unnormalized half-weighted Chebyshev sum. -/
theorem vonMangoldtPerronIntegral_tendsto_psi (x c : ℝ) (hx : 0 < x) (hc : 1 < c) :
    Tendsto (vonMangoldtPerronIntegral x c) atTop
      (𝓝 (2 * (Real.pi : ℂ) * (halfWeightedChebyshevPsi x : ℂ))) := by
  have hbound := (eventually_gt_atTop (0 : ℝ)).mono
    (fun T hT => vonMangoldtPerronIntegral_sub_psi_bound x c T hx hc hT)
  have hlim (C : ℝ) : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.const_mul C)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall (fun _ =>
    norm_nonneg _)) hbound (hlim _))

#print axioms perronTruncatedKernel_at_jump_bound
#print axioms div_max_le_abs_log_div
#print axioms summable_perronSeriesErrorMajorant
#print axioms perronSeriesError_le_majorant
#print axioms perronSeries_sub_step_bound
#print axioms vonMangoldt_perron_step
#print axioms vonMangoldtPerronIntegral_sub_psi_bound
#print axioms vonMangoldtPerronIntegral_tendsto_psi
end RiemannResearch

namespace RiemannResearch
open Filter Set
open scoped Topology

/-- On the two sides of a half-integer the reciprocal distances run
through the same list, and each is bounded by twice a harmonic summand. -/
theorem halfInteger_reciprocal_distances_le (m : ℕ) :
    (∑ n ∈ Finset.range (2 * (m + 1)), |(m : ℝ) + 1 / 2 - n|⁻¹) ≤
      4 * (1 + Real.log ((m : ℝ) + 1)) := by
  let f (n : ℕ) := |(m : ℝ) + 1 / 2 - n|⁻¹
  have hleft : (∑ n ∈ Finset.range (m + 1), f n) =
      ∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1 / 2)⁻¹ := by
    rw [← Finset.sum_range_reflect f (m + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hd : (m : ℝ) + 1 / 2 - ((m + 1 - 1 - j : ℕ) : ℝ) = (j : ℝ) + 1 / 2 := by
      rw [Nat.add_sub_cancel, Nat.cast_sub hle]
      ring
    simp only [f, hd, abs_of_nonneg (show 0 ≤ (j : ℝ) + 1 / 2 by positivity)]
  have hright : (∑ n ∈ Finset.range (m + 1), f (m + 1 + n)) =
      ∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1 / 2)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j _
    have hd : (m : ℝ) + 1 / 2 - ((m + 1 + j : ℕ) : ℝ) = -((j : ℝ) + 1 / 2) := by
      push_cast
      ring
    simp only [f, hd, abs_neg, abs_of_nonneg (show 0 ≤ (j : ℝ) + 1 / 2 by positivity)]
  have hsum : (∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1 / 2)⁻¹) ≤
      2 * (1 + Real.log ((m : ℝ) + 1)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), 2 * ((j : ℝ) + 1)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
        rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
        exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
      _ = 2 * (harmonic (m + 1) : ℝ) := by
        rw [← Finset.mul_sum, harmonic]
        push_cast
        rfl
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (m + 1)) (by norm_num : (0 : ℝ) ≤ 2)
  change (∑ n ∈ Finset.range (2 * (m + 1)), f n) ≤ _
  rw [two_mul, Finset.sum_range_add, hleft, hright]
  linarith [hsum]

/-- Every half-integer cutoff with nonnegative integer part is positive
and stays off the jump of every positive integer Dirichlet term. -/
theorem halfInteger_ne_natCast (m n : ℕ) : (m : ℝ) + 1 / 2 ≠ (n : ℝ) := by
  intro h
  have hf : ⌊(m : ℝ) + 1 / 2⌋₊ = m := by
    apply (Nat.floor_eq_iff (by positivity)).mpr
    constructor <;> linarith
  rw [h, Nat.floor_natCast] at hf
  rw [hf] at h
  linarith

/-- The finite part of the majorant uses reciprocal distances. The other
indices are controlled directly by the absolutely convergent Dirichlet series. -/
theorem perronMajorant_halfInteger_term_le (m n : ℕ) (c : ℝ) (hc : 1 < c) (hc₂ : c ≤ 2) :
    let x : ℝ := (m : ℝ) + 1 / 2
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ)
    perronSeriesErrorMajorant f x c n ≤
      ‖LSeries.term f (c : ℂ) n‖ * (x ^ c * (8 + 4 / Real.log 2)) +
      if n < 2 * (m + 1) then (32 * x * Real.log (2 * x)) * |x - n|⁻¹ else 0 := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ)
  change perronSeriesErrorMajorant f x c n ≤
    ‖LSeries.term f (c : ℂ) n‖ * (x ^ c * (8 + 4 / Real.log 2)) +
    if n < 2 * (m + 1) then (32 * x * Real.log (2 * x)) * |x - n|⁻¹ else 0
  have hx : 0 < x := by dsimp [x]; positivity
  have h2x : 1 ≤ 2 * x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hlog : 0 ≤ Real.log (2 * x) := Real.log_nonneg h2x
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmain : 0 ≤ ‖LSeries.term f (c : ℂ) n‖ * (x ^ c * (8 + 4 / Real.log 2)) := by
    positivity
  have hnear : 0 ≤ (if n < 2 * (m + 1) then
      (32 * x * Real.log (2 * x)) * |x - n|⁻¹ else 0) := by
    split_ifs <;> positivity
  by_cases hn : n = 0
  · rw [perronSeriesErrorMajorant, if_pos hn]
    exact add_nonneg hmain hnear
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hne : x ≠ (n : ℝ) := halfInteger_ne_natCast m n
  rw [perronSeriesErrorMajorant, if_neg hn]
  by_cases hfar : 2 * x ≤ (n : ℝ)
  · rw [if_pos hfar]
    refine le_add_of_le_of_nonneg ?_ hnear
    gcongr
    linarith
  rw [if_neg hfar, if_neg hne]
  by_cases hleft : 2 * (n : ℝ) ≤ x
  · have hnle : (n : ℝ) ≤ x := by linarith
    have hgap : (1 / 2 : ℝ) ≤ |x - (n : ℝ)| / max x (n : ℝ) := by
      rw [max_eq_left hnle, abs_of_nonneg (sub_nonneg.mpr hnle), le_div_iff₀ hx]
      have hh : (n : ℝ) ≤ x / 2 :=
        (le_div_iff₀ (by norm_num)).mpr (by simpa only [mul_comm] using hleft)
      calc
        (1 / 2 : ℝ) * x = x - x / 2 := by ring
        _ ≤ x - (n : ℝ) := sub_le_sub_left hh _
    have hrec : 4 / (|x - (n : ℝ)| / max x (n : ℝ)) ≤ 8 := by
      have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 4 by norm_num)
        (show (0 : ℝ) < 1 / 2 by norm_num) hgap
      norm_num at h ⊢
      exact h
    refine le_add_of_le_of_nonneg ?_ hnear
    calc
      _ ≤ ‖f n‖ * ((x / (n : ℝ)) ^ c * 8) := by gcongr
      _ = ‖LSeries.term f (↑c) n‖ * (x ^ c * 8) := by
        rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, Real.div_rpow hx.le hnpos.le]
        ring
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right (div_nonneg (by norm_num) hlog2.le)
  · have hnt : (n : ℝ) < 2 * x := lt_of_not_ge hfar
    have hindex : n < 2 * (m + 1) := by
      have h : (n : ℝ) < ((2 * (m + 1) : ℕ) : ℝ) := by
        push_cast
        dsimp [x] at hnt
        linarith
      exact_mod_cast h
    rw [if_pos hindex]
    refine le_add_of_nonneg_of_le hmain ?_
    have hy : (x / (n : ℝ)) ^ c ≤ 4 := by
      calc
        _ ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow (div_nonneg hx.le hnpos.le)
          ((div_le_iff₀ hnpos).mpr (le_of_not_ge hleft)) (by linarith)
        _ ≤ (2 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc₂
        _ = 4 := by norm_num
    have hΛ : ‖f n‖ ≤ Real.log (2 * x) := by
      rw [show f n = (ArithmeticFunction.vonMangoldt n : ℂ) by rfl, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hnt.le)
    have hmax : max x (n : ℝ) ≤ 2 * x := max_le (by linarith) hnt.le
    calc
      _ = ‖f n‖ * ((x / (n : ℝ)) ^ c * (4 * max x (n : ℝ) * |x - n|⁻¹)) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc]
      _ ≤ Real.log (2 * x) * (4 * (4 * (2 * x) * |x - n|⁻¹)) := by gcongr
      _ = _ := by ring

/-- For half-integer cutoffs the sum of the error coefficients is controlled
by the absolute Dirichlet series and an elementary logarithmic term. -/
theorem perronMajorant_halfInteger_tsum_le (m : ℕ) (c : ℝ) (hc : 1 < c) (hc₂ : c ≤ 2) :
    let x : ℝ := (m : ℝ) + 1 / 2
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ)
    (∑' n : ℕ, perronSeriesErrorMajorant f x c n) ≤
      (∑' n : ℕ, ‖LSeries.term f (c : ℂ) n‖) * (x ^ c * (8 + 4 / Real.log 2)) +
        128 * x * Real.log (2 * x) * (1 + Real.log (2 * x)) := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ)
  change (∑' n : ℕ, perronSeriesErrorMajorant f x c n) ≤ _
  let A (n : ℕ) := ‖LSeries.term f (c : ℂ) n‖ * (x ^ c * (8 + 4 / Real.log 2))
  let B (n : ℕ) := if n < 2 * (m + 1) then (32 * x * Real.log (2 * x)) * |x - n|⁻¹ else 0
  have hx : 0 < x := by dsimp [x]; positivity
  have hf : LSeriesSummable f (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa)
  have hA : Summable A := (summable_norm_iff.mpr hf).mul_right _
  have hB0 : ∀ n ∉ Finset.range (2 * (m + 1)), B n = 0 := by
    intro n hn
    simp only [B, ← Finset.mem_range, if_neg hn]
  have hB := summable_of_ne_finset_zero hB0
  have h := (summable_perronSeriesErrorMajorant f x c hx hf).tsum_le_tsum
    (fun n => perronMajorant_halfInteger_term_le m n c hc hc₂) (hA.add hB)
  rw [hA.tsum_add hB, tsum_eq_sum hB0] at h
  have hsum : (∑ n ∈ Finset.range (2 * (m + 1)), B n) =
      (32 * x * Real.log (2 * x)) *
        (∑ n ∈ Finset.range (2 * (m + 1)), |x - n|⁻¹) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ hn => if_pos (Finset.mem_range.mp hn)
  have hlog : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m])
  have hlog' : Real.log ((m : ℝ) + 1) ≤ Real.log (2 * x) :=
    Real.log_le_log (by positivity) (by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) m])
  have hAeq : (∑' n, A n) = (∑' n, ‖LSeries.term f (c : ℂ) n‖) *
      (x ^ c * (8 + 4 / Real.log 2)) := tsum_mul_right
  rw [hAeq, hsum] at h
  apply h.trans
  apply add_le_add_left
  calc
    _ ≤ (32 * x * Real.log (2 * x)) * (4 * (1 + Real.log ((m : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (halfInteger_reciprocal_distances_le m) (by positivity)
    _ ≤ (32 * x * Real.log (2 * x)) * (4 * (1 + Real.log (2 * x))) := by gcongr
    _ = _ := by ring

/-- Half-integer cutoffs give the ordinary Chebyshev sum and a logarithmic
bound on the near-cutoff contribution to the Perron truncation. -/
theorem vonMangoldtPerronIntegral_halfInteger_bound (m : ℕ) (c T : ℝ)
    (hc : 1 < c) (hc₂ : c ≤ 2) (hT : 0 < T) :
    let x : ℝ := (m : ℝ) + 1 / 2
    let f : ℕ → ℂ := fun k => (ArithmeticFunction.vonMangoldt k : ℂ)
    ‖vonMangoldtPerronIntegral x c T - 2 * (Real.pi : ℂ) * (chebyshevPsi x : ℂ)‖ ≤
      ((∑' n : ℕ, ‖LSeries.term f (c : ℂ) n‖) * (x ^ c * (8 + 4 / Real.log 2)) +
        128 * x * Real.log (2 * x) * (1 + Real.log (2 * x))) / T := by
  let x : ℝ := (m : ℝ) + 1 / 2
  change ‖vonMangoldtPerronIntegral x c T - 2 * (Real.pi : ℂ) * (chebyshevPsi x : ℂ)‖ ≤ _
  have hx : 0 < x := by dsimp [x]; positivity
  have hhalf : halfWeightedChebyshevPsi x = chebyshevPsi x := by
    rw [halfWeightedChebyshevPsi, if_neg (halfInteger_ne_natCast m ⌊x⌋₊), sub_zero]
  have h := vonMangoldtPerronIntegral_sub_psi_bound x c T hx hc hT
  rw [hhalf] at h
  exact h.trans (div_le_div_of_nonneg_right (perronMajorant_halfInteger_tsum_le m c hc hc₂) hT.le)

/-- The von Mangoldt Dirichlet series on the real axis is a sum of its
nonnegative term norms. -/
theorem vonMangoldt_tsum_norm_term (c : ℝ) :
    let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
    ((∑' n : ℕ, ‖LSeries.term f (c : ℂ) n‖ : ℝ) : ℂ) = LSeries f (c : ℂ) := by
  dsimp only
  rw [Complex.ofReal_tsum, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re, LSeries.term_of_ne_zero hn,
    Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]

/-- Removing the simple pole of the zeta logarithmic derivative gives a
bounded function on the real segment from 1 to 2. -/
theorem vonMangoldt_tsum_norm_term_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 < c → c ≤ 2 →
      (∑' n : ℕ, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (c : ℂ) n‖) ≤ 1 / (c - 1) + K := by
  let U (t : ℝ) := deriv regularizedZeta (t : ℂ) / regularizedZeta (t : ℂ)
  have hne (t : ℝ) (ht : 1 ≤ t) : regularizedZeta (t : ℂ) ≠ 0 := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, Complex.ofReal_one, regularizedZeta_one]
      exact one_ne_zero
    · have ht1 : (t : ℂ) ≠ 1 := by exact_mod_cast h.ne'
      rw [(regularizedZeta_eventuallyEq (t : ℂ) ht1).eq_of_nhds]
      exact mul_ne_zero (sub_ne_zero.mpr ht1)
        (riemannZeta_ne_zero_of_one_le_re (by simpa using ht))
  have hU : ContinuousOn (fun t => ‖U t‖) (Icc (1 : ℝ) 2) := by
    have hd : Continuous (deriv regularizedZeta) :=
      continuous_iff_continuousAt.mpr fun z => (regularizedZeta_analyticAt z).deriv.continuousAt
    have hcont : Continuous regularizedZeta :=
      continuous_iff_continuousAt.mpr fun z => (regularizedZeta_analyticAt z).continuousAt
    exact ((hd.comp Complex.continuous_ofReal).continuousOn.div
      (hcont.comp Complex.continuous_ofReal).continuousOn (fun t ht => hne t ht.1)).norm
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hU
  have hBound (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) : ‖U t‖ ≤ K :=
    hK (mem_image_of_mem _ ht)
  refine ⟨K, (norm_nonneg _).trans (hBound 1 (by norm_num)), fun c hc hc₂ => ?_⟩
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hc).ne'
  have hc1 : (c : ℂ) ≠ 1 := by exact_mod_cast hc.ne'
  have hζ := riemannZeta_ne_zero_of_one_le_re (show 1 ≤ (c : ℂ).re by simpa using hc.le)
  have hreg := regularizedZeta_mellin_eq (c : ℂ) hc0 hc1 hζ
  have hL : LSeries (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (c : ℂ) =
      1 / ((c : ℂ) - 1) - U c := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hc)]
    let w := -deriv riemannZeta (c : ℂ) / riemannZeta (c : ℂ)
    change w = _
    change -(1 + U c) / (c : ℂ) = -1 / ((c : ℂ) - 1) + w / (c : ℂ) at hreg
    have hd : (c : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have hscaled : -(1 + U c) = -(c : ℂ) / ((c : ℂ) - 1) + w := by
      have hh := congrArg (fun z : ℂ => z * (c : ℂ)) hreg
      dsimp only at hh
      rw [add_mul, div_mul_cancel₀ _ hc0, div_mul_cancel₀ _ hc0, div_mul_eq_mul_div,
        neg_one_mul] at hh
      exact hh
    have hsplit : (c : ℂ) / ((c : ℂ) - 1) = 1 + 1 / ((c : ℂ) - 1) := by
      field_simp [hd]
    rw [neg_div, hsplit] at hscaled
    linear_combination -hscaled
  have hreal := congrArg Complex.re ((vonMangoldt_tsum_norm_term c).trans hL)
  have hdiv : (1 : ℂ) / ((c : ℂ) - 1) = ((1 / (c - 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hdiv, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_re] at hreal
  rw [hreal]
  have hRe := Complex.abs_re_le_norm (U c)
  have hKc := hBound c ⟨hc.le, hc₂⟩
  linarith [neg_abs_le (U c).re]

/-- On the moving line c = 1 + 1/log x the half-integer truncation error
is bounded by a constant times x (1 + log (2x))² / T. -/
theorem vonMangoldtPerronIntegral_halfInteger_moving_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (T : ℝ), 0 < T →
      let x : ℝ := (m : ℝ) + 1 / 2
      1 ≤ Real.log x →
      ‖vonMangoldtPerronIntegral x (1 + (Real.log x)⁻¹) T -
          2 * (Real.pi : ℂ) * (chebyshevPsi x : ℂ)‖ ≤
        C * x * (1 + Real.log (2 * x)) ^ 2 / T := by
  obtain ⟨K, hK, hn⟩ := vonMangoldt_tsum_norm_term_le
  let A := Real.exp 1 * (8 + 4 / Real.log 2)
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A * (1 + K) + 128, add_nonneg (mul_nonneg hA (by linarith)) (by norm_num),
    fun m T hT => ?_⟩
  let x : ℝ := (m : ℝ) + 1 / 2
  change 1 ≤ Real.log x → _
  intro hxlog
  have hx : 0 < x := by dsimp [x]; positivity
  have hlog : 0 < Real.log x := zero_lt_one.trans_le hxlog
  let c := 1 + (Real.log x)⁻¹
  have hc : 1 < c := lt_add_of_pos_right 1 (inv_pos.mpr hlog)
  have hc₂ : c ≤ 2 := by
    have h := inv_le_one_of_one_le₀ hxlog
    dsimp [c]
    linarith
  have hcsub : c - 1 = (Real.log x)⁻¹ := by dsimp [c]; ring
  have hp : x ^ c = x * Real.exp 1 := by
    dsimp [c]
    rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_def_of_pos hx,
      mul_inv_cancel₀ hlog.ne']
  let L := Real.log (2 * x)
  have hxL : Real.log x ≤ L := Real.log_le_log hx (by linarith)
  have hL : 0 ≤ L := hlog.le.trans hxL
  have hlogSq : L + K ≤ (1 + K) * (1 + L) ^ 2 := by
    have h₁ : L + K ≤ (1 + K) * (1 + L) := by nlinarith
    refine h₁.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    nlinarith [sq_nonneg L]
  have hseries := hn c hc hc₂
  rw [hcsub, one_div, inv_inv] at hseries
  refine (vonMangoldtPerronIntegral_halfInteger_bound m c T hc hc₂ hT).trans
    (div_le_div_of_nonneg_right ?_ hT.le)
  change (∑' n : ℕ, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (c : ℂ) n‖) * (x ^ c * (8 + 4 / Real.log 2)) + 128 * x * L * (1 + L) ≤ _
  rw [hp, mul_assoc, ← show A = Real.exp 1 * (8 + 4 / Real.log 2) from rfl]
  have hmain := mul_le_mul_of_nonneg_right ((hseries.trans (add_le_add_right hxL K)).trans hlogSq)
    (show 0 ≤ x * A by positivity)
  have hnear := mul_le_mul_of_nonneg_left
    (show L * (1 + L) ≤ (1 + L) ^ 2 by nlinarith) (show 0 ≤ 128 * x by positivity)
  calc
    _ ≤ ((1 + K) * (1 + L) ^ 2) * (x * A) + (128 * x) * (1 + L) ^ 2 := by
      rw [mul_assoc (128 * x)]
      exact add_le_add hmain hnear
    _ = _ := by change _ = (A * (1 + K) + 128) * x * (1 + L) ^ 2; ring

#print axioms halfInteger_reciprocal_distances_le
#print axioms halfInteger_ne_natCast
#print axioms perronMajorant_halfInteger_term_le
#print axioms perronMajorant_halfInteger_tsum_le
#print axioms vonMangoldtPerronIntegral_halfInteger_bound
#print axioms vonMangoldt_tsum_norm_term
#print axioms vonMangoldt_tsum_norm_term_le
#print axioms vonMangoldtPerronIntegral_halfInteger_moving_bound
end RiemannResearch

namespace RiemannResearch
open Filter Set MeasureTheory
open scoped Interval Topology

/-- A vertical segment parametrized by its imaginary coordinate. -/
noncomputable def perronVertical (f : ℂ → ℂ) (r T : ℝ) : ℂ :=
  ∫ t in -T..T, f ((r : ℂ) + (t : ℂ) * Complex.I)

/-- A horizontal segment parametrized by its real coordinate. -/
noncomputable def perronHorizontal (f : ℂ → ℂ) (a b h : ℝ) : ℂ :=
  ∫ t in a..b, f ((t : ℂ) + (h : ℂ) * Complex.I)

/-- The rectangle boundary integral divided by i, in counterclockwise orientation. -/
noncomputable def perronRectangle (f : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  perronVertical f b T - perronVertical f a T +
    Complex.I * (perronHorizontal f a b T - perronHorizontal f a b (-T))

/-- Cauchy–Goursat in vertical integral units. -/
theorem perronRectangle_eq_zero (f : ℂ → ℂ) (a b T : ℝ)
    (hf : ∀ z : ℂ, z.re ∈ [[a, b]] → DifferentiableAt ℂ f z) :
    perronRectangle f a b T = 0 := by
  let z : ℂ := (a : ℂ) - (T : ℂ) * Complex.I
  let w : ℂ := (b : ℂ) + (T : ℂ) * Complex.I
  have hzre : z.re = a := by simp [z, Complex.mul_re]
  have hwre : w.re = b := by simp [w, Complex.mul_re]
  have hzim : z.im = -T := by simp [z, Complex.mul_im]
  have hwim : w.im = T := by simp [w, Complex.mul_im]
  have hd : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro v hv
    apply (hf v ?_).differentiableWithinAt
    simpa only [← hzre, ← hwre] using hv.1
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hd
  simp only [hzre, hwre, hzim, hwim, Complex.ofReal_neg, smul_eq_mul] at hrect
  unfold perronRectangle perronVertical perronHorizontal
  push_cast
  have halgebra (L R B U : ℂ) (h : B - U + Complex.I * R - Complex.I * L = 0) :
      R - L + Complex.I * (U - B) = 0 := by
    linear_combination (norm := skip) -Complex.I * h
    ring_nf
    simp [Complex.I_sq]
  exact halgebra _ _ _ _ hrect

/-- A reciprocal has the arctangent vertical primitive on a positive line. -/
theorem perronVertical_inv_pos (c T : ℝ) (hc : 0 < c) :
    perronVertical (fun z => z⁻¹) c T = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
  simpa [perronVertical, perronOscillatoryKernel, one_div] using
    perronOscillatoryKernel_integral_zero c T hc

/-- Reflection changes the sign of the reciprocal's vertical integral. -/
theorem perronVertical_inv_neg (c T : ℝ) (hc : c < 0) :
    perronVertical (fun z => z⁻¹) c T = -((2 * Real.arctan (T / (-c)) : ℝ) : ℂ) := by
  have he := perron_exp_vertical_reflect 0 (-c) T
  simp only [neg_neg, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_div] at he
  change perronVertical (fun z => z⁻¹) c T = -perronVertical (fun z => z⁻¹) (-c) T at he
  rw [he, perronVertical_inv_pos _ _ (neg_pos.mpr hc)]

/-- The difference of the two horizontal reciprocal integrals is an
arctangent difference, in vertical units. -/
theorem perronHorizontal_inv_diff (a b T : ℝ) (hT : 0 < T) :
    Complex.I * (perronHorizontal (fun z => z⁻¹) a b T -
      perronHorizontal (fun z => z⁻¹) a b (-T)) =
      ((2 * (Real.arctan (b / T) - Real.arctan (a / T)) : ℝ) : ℂ) := by
  have hcont (h : ℝ) (hh : h ≠ 0) :
      Continuous (fun t : ℝ => ((t : ℂ) + (h : ℂ) * Complex.I)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t hz
    exact hh (by simpa [Complex.mul_im] using congrArg Complex.im hz)
  unfold perronHorizontal
  rw [← intervalIntegral.integral_sub ((hcont T hT.ne').intervalIntegrable a b)
    ((hcont (-T) (neg_ne_zero.mpr hT.ne')).intervalIntegrable a b),
    ← intervalIntegral.integral_const_mul]
  have hpoint (t : ℝ) : Complex.I *
      (((t : ℂ) + (T : ℂ) * Complex.I)⁻¹ - ((t : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)⁻¹) =
      ((2 * (T⁻¹ * (1 + (t / T) ^ 2)⁻¹) : ℝ) : ℂ) := by
    have hd : (t : ℂ) + (T : ℂ) * Complex.I ≠ 0 := fun h => hT.ne' (by
      simpa [Complex.mul_im] using congrArg Complex.im h)
    have he : (t : ℂ) - (T : ℂ) * Complex.I ≠ 0 := fun h => hT.ne' (by
      simpa [Complex.mul_im] using congrArg Complex.im h)
    have hsum : 0 < T ^ 2 + t ^ 2 := by positivity
    have hval : 2 * (T⁻¹ * (1 + (t / T) ^ 2)⁻¹) = 2 * T / (T ^ 2 + t ^ 2) := by
      have hk : (1 : ℝ) + (t / T) ^ 2 = (T ^ 2 + t ^ 2) / T ^ 2 := by
        field_simp
      rw [hk, inv_div]
      field_simp
      ring
    rw [hval]
    push_cast
    rw [neg_mul, ← sub_eq_add_neg]
    have hk : (T : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hsum.ne'
    field_simp [hd, he, hk]
    ring_nf
    simp [Complex.I_sq]
    ring
  simp_rw [hpoint]
  have hreal :
      (∫ t in a..b, T⁻¹ * (1 + (t / T) ^ 2)⁻¹) =
      Real.arctan (b / T) - Real.arctan (a / T) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) hT.ne']
    simp [smul_eq_mul, hT.ne', integral_inv_one_add_sq]
  have hc : Continuous (fun t : ℝ => T⁻¹ * (1 + (t / T) ^ 2)⁻¹) :=
    continuous_const.mul ((continuous_const.add ((continuous_id.div_const T).pow 2)).inv₀
      (fun t => by positivity))
  have hlin := Complex.ofRealCLM.intervalIntegral_comp_comm
    (((continuous_const : Continuous (fun _ : ℝ => (2 : ℝ))).mul hc).intervalIntegrable
      (μ := volume) a b)
  change (∫ t in a..b, ((2 * (T⁻¹ * (1 + (t / T) ^ 2)⁻¹) : ℝ) : ℂ)) =
    (↑(∫ t in a..b, (2 : ℝ) * (T⁻¹ * (1 + (t / T) ^ 2)⁻¹)) : ℂ) at hlin
  rw [hlin, intervalIntegral.integral_const_mul, hreal]

/-- A centered rectangular contour encloses the unit residue of 1/z. -/
theorem perronRectangle_inv (a b T : ℝ) (ha : a < 0) (hb : 0 < b) (hT : 0 < T) :
    perronRectangle (fun z => z⁻¹) a b T = 2 * (Real.pi : ℂ) := by
  rw [perronRectangle, perronVertical_inv_pos b T hb, perronVertical_inv_neg a T ha,
    perronHorizontal_inv_diff a b T hT]
  have hleft := Real.arctan_inv_of_pos (div_pos hT (neg_pos.mpr ha))
  have hright := Real.arctan_inv_of_pos (div_pos hT hb)
  rw [inv_div, neg_div, Real.arctan_neg] at hleft
  rw [inv_div] at hright
  exact_mod_cast (show
    2 * Real.arctan (T / b) - -(2 * Real.arctan (T / (-a))) +
      2 * (Real.arctan (b / T) - Real.arctan (a / T)) = 2 * Real.pi by linarith)

/-- Translating the simple pole along the real axis translates the two
horizontal endpoints and the real coordinates of the two vertical edges. -/
theorem perronRectangle_inv_sub_real (p a b T : ℝ) (ha : a < p) (hb : p < b) (hT : 0 < T) :
    perronRectangle (fun z => (z - (p : ℂ))⁻¹) a b T = 2 * (Real.pi : ℂ) := by
  have hv (r : ℝ) :
      perronVertical (fun z => (z - (p : ℂ))⁻¹) r T =
      perronVertical (fun z => z⁻¹) (r - p) T := by
    unfold perronVertical
    simp only [Complex.ofReal_sub]
    congr 1
    ext t
    congr 1
    ring
  have hh (h : ℝ) :
      perronHorizontal (fun z => (z - (p : ℂ))⁻¹) a b h =
      perronHorizontal (fun z => z⁻¹) (a - p) (b - p) h := by
    let g (t : ℝ) := ((t : ℂ) + (h : ℂ) * Complex.I)⁻¹
    rw [perronHorizontal, perronHorizontal, ← intervalIntegral.integral_comp_sub_right g p]
    congr 1
    ext t
    dsimp [g]
    rw [Complex.ofReal_sub]
    congr 1
    ring
  simp_rw [perronRectangle, hv, hh]
  exact perronRectangle_inv (a - p) (b - p) T (sub_neg.mpr ha) (sub_pos.mpr hb) hT

/-- The regular part obtained by subtracting the simple pole of residue x. -/
noncomputable def zetaPerronRegularPart (x : ℝ) (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp ((Real.log x : ℂ) * w)) 1 z -
    Complex.exp ((Real.log x : ℂ) * z) *
      ((1 + deriv regularizedZeta z / regularizedZeta z) / z)

theorem zetaPerronRegularPart_analyticAt (x : ℝ) (z : ℂ)
    (hz : z ≠ 0) (hU : regularizedZeta z ≠ 0) :
    AnalyticAt ℂ (zetaPerronRegularPart x) z := by
  let E : ℂ → ℂ := fun w => Complex.exp ((Real.log x : ℂ) * w)
  have hE (w : ℂ) : AnalyticAt ℂ E w := (analyticAt_const.mul analyticAt_id).cexp
  have hds : AnalyticAt ℂ (dslope E 1) z := by
    by_cases h : z = 1
    · subst z
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin] with w hw
        exact (differentiableAt_dslope_of_ne hw).mpr (hE w).differentiableAt
      · exact continuousAt_dslope_same.mpr (hE 1).differentiableAt
    · apply AnalyticAt.congr
        ((((hE z).sub (analyticAt_const (v := E 1))).div (analyticAt_id.sub analyticAt_const))
          (sub_ne_zero.mpr h))
      filter_upwards [eventually_ne_nhds h] with w hw
      rw [dslope_of_ne E hw, slope_def_field]
      rfl
  have hA := regularizedZeta_analyticAt z
  exact hds.sub ((hE z).mul ((analyticAt_const.add (hA.deriv.div hA hU)).div analyticAt_id hz))

/-- Away from the pole, the original integrand equals the regular part
plus x/(z-1). -/
theorem zetaPerronIntegrand_eq_regular_add (x : ℝ) (hx : 0 < x) (z : ℂ)
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hζ : riemannZeta z ≠ 0) :
    zetaPerronIntegrand x z = zetaPerronRegularPart x z + (x : ℂ) * (z - 1)⁻¹ := by
  have hE : (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le]
  have hE1 : Complex.exp ((Real.log x : ℂ) * (1 : ℂ)) = (x : ℂ) := by
    rw [mul_one, ← Complex.ofReal_exp, Real.exp_log hx]
  have hm := regularizedZeta_mellin_eq z hz0 hz1 hζ
  rw [zetaPerronIntegrand, zetaPerronRegularPart, dslope_of_ne _ hz1, slope_def_field, hE1, hE]
  linear_combination (norm := ring_nf) -Complex.exp ((Real.log x : ℂ) * z) * hm

/-- The finite rectangle picks up 2π times the coefficient of a real pole
when the remaining integrand is holomorphic on the closed strip. -/
theorem perronRectangle_of_real_pole (f g : ℂ → ℂ) (p a b T : ℝ) (r : ℂ)
    (ha : a < p) (hb : p < b) (hT : 0 < T)
    (hg : ∀ z : ℂ, z.re ∈ [[a, b]] → DifferentiableAt ℂ g z)
    (hf : ∀ z : ℂ, z.re ∈ [[a, b]] → z ≠ (p : ℂ) →
      f z = g z + r * (z - (p : ℂ))⁻¹) :
    perronRectangle f a b T = r * (2 * (Real.pi : ℂ)) := by
  let P (z : ℂ) := (z - (p : ℂ))⁻¹
  have hind (l u : ℝ) (γ : ℝ → ℂ) (hγ : Continuous γ)
      (hstrip : ∀ t ∈ [[l,u]], (γ t).re ∈ [[a,b]])
      (hne : ∀ t ∈ [[l,u]], γ t ≠ (p : ℂ)) :
      (∫ t in l..u, f (γ t)) = (∫ t in l..u, g (γ t)) + r * ∫ t in l..u, P (γ t) := by
    have hg' : ContinuousOn (fun t => g (γ t)) [[l,u]] := by
      intro t ht
      exact (hg _ (hstrip t ht)).continuousAt.comp_continuousWithinAt hγ.continuousWithinAt
    have hp : ContinuousOn (fun t => P (γ t)) [[l,u]] :=
      (hγ.sub continuous_const).continuousOn.inv₀ (fun t ht => sub_ne_zero.mpr (hne t ht))
    calc
      _ = ∫ t in l..u, g (γ t) + r * P (γ t) :=
        intervalIntegral.integral_congr (fun t ht => hf _ (hstrip t ht) (hne t ht))
      _ = _ := by
        rw [intervalIntegral.integral_add hg'.intervalIntegrable (hp.intervalIntegrable.const_mul r),
          intervalIntegral.integral_const_mul]
  have hV (c : ℝ) (hc : c ∈ [[a,b]]) (hcp : c ≠ p) :
      perronVertical f c T = perronVertical g c T + r * perronVertical P c T := by
    apply hind (-T) T _ (by fun_prop)
    · intro t _
      simpa [Complex.mul_re] using hc
    · intro t _ ht
      exact hcp (by simpa [Complex.mul_re] using congrArg Complex.re ht)
  have hH (c : ℝ) (hc : c ≠ 0) :
      perronHorizontal f a b c = perronHorizontal g a b c + r * perronHorizontal P a b c := by
    apply hind a b _ (by fun_prop)
    · intro t ht
      simpa [Complex.mul_re] using ht
    · intro t _ ht
      exact hc (by simpa [Complex.mul_im] using congrArg Complex.im ht)
  calc
    _ = perronRectangle g a b T + r * perronRectangle P a b T := by
      unfold perronRectangle
      rw [hV b right_mem_uIcc hb.ne', hV a left_mem_uIcc ha.ne,
        hH T hT.ne', hH (-T) (neg_ne_zero.mpr hT.ne')]
      ring
    _ = _ := by
      rw [perronRectangle_eq_zero g a b T hg, zero_add, perronRectangle_inv_sub_real p a b T ha hb hT]

/-- On a positive strip free of zeta zeros, crossing 1 contributes the
Perron main term. The formula retains both horizontal edges. -/
theorem vonMangoldtPerronIntegral_shift (x a b T : ℝ) (hx : 0 < x)
    (ha0 : 0 < a) (ha1 : a < 1) (hb : 1 < b) (hT : 0 < T)
    (hζ : ∀ z : ℂ, z.re ∈ [[a, b]] → z ≠ 1 → riemannZeta z ≠ 0) :
    vonMangoldtPerronIntegral x b T - 2 * (Real.pi : ℂ) * (x : ℂ) =
      vonMangoldtPerronIntegral x a T -
        Complex.I * (perronHorizontal (zetaPerronIntegrand x) a b T -
          perronHorizontal (zetaPerronIntegrand x) a b (-T)) := by
  have hab : a ≤ b := (ha1.trans hb).le
  have hz0 (z : ℂ) (hz : z.re ∈ [[a,b]]) : z ≠ 0 := by
    rw [uIcc_of_le hab] at hz
    exact Complex.ne_zero_of_re_pos (ha0.trans_le hz.1)
  have hU (z : ℂ) (hz : z.re ∈ [[a,b]]) : regularizedZeta z ≠ 0 := by
    by_cases h : z = 1
    · simp [h]
    rw [(regularizedZeta_eventuallyEq z h).eq_of_nhds]
    exact mul_ne_zero (sub_ne_zero.mpr h) (hζ z hz h)
  have h := perronRectangle_of_real_pole (zetaPerronIntegrand x) (zetaPerronRegularPart x)
    1 a b T (x : ℂ) ha1 hb hT
    (fun z hz => (zetaPerronRegularPart_analyticAt x z (hz0 z hz) (hU z hz)).differentiableAt)
    (fun z hz h1 => by simpa only [Complex.ofReal_one] using
      zetaPerronIntegrand_eq_regular_add x hx z (hz0 z hz) h1 (hζ z hz h1))
  change vonMangoldtPerronIntegral x b T - vonMangoldtPerronIntegral x a T +
    Complex.I * (perronHorizontal (zetaPerronIntegrand x) a b T -
      perronHorizontal (zetaPerronIntegrand x) a b (-T)) = (x : ℂ) * (2 * (Real.pi : ℂ)) at h
  linear_combination h

/-- Under RH the finite Perron contour may be shifted across the pole at
1 to any line strictly between the critical line and the pole. -/
theorem vonMangoldtPerronIntegral_shift_of_RH (hRH : RiemannHypothesis)
    (x a b T : ℝ) (hx : 0 < x) (ha : 1 / 2 < a) (ha1 : a < 1) (hb : 1 < b) (hT : 0 < T) :
    vonMangoldtPerronIntegral x b T - 2 * (Real.pi : ℂ) * (x : ℂ) =
      vonMangoldtPerronIntegral x a T -
        Complex.I * (perronHorizontal (zetaPerronIntegrand x) a b T -
          perronHorizontal (zetaPerronIntegrand x) a b (-T)) := by
  apply vonMangoldtPerronIntegral_shift x a b T hx ((by norm_num : (0 : ℝ) < 1 / 2).trans ha)
    ha1 hb hT
  intro z hz _
  rw [uIcc_of_le (ha1.trans hb).le] at hz
  exact riemannZeta_ne_zero_right_of_riemannHypothesis hRH z (ha.trans_le hz.1)

/-- Combining truncation with the RH contour shift bounds the Chebyshev
error by the new vertical edge, the two horizontal edges, and truncation. -/
theorem chebyshevPsi_halfInteger_bound_of_RH (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (a T : ℝ), 1 / 2 < a → a < 1 → 0 < T →
      let x : ℝ := (m : ℝ) + 1 / 2
      let b := 1 + (Real.log x)⁻¹
      1 ≤ Real.log x →
      ‖2 * (Real.pi : ℂ) * ((chebyshevPsi x : ℂ) - (x : ℂ))‖ ≤
        C * x * (1 + Real.log (2 * x)) ^ 2 / T +
          (‖vonMangoldtPerronIntegral x a T‖ +
            ‖perronHorizontal (zetaPerronIntegrand x) a b T‖ +
            ‖perronHorizontal (zetaPerronIntegrand x) a b (-T)‖) := by
  obtain ⟨C, hC, htrunc⟩ := vonMangoldtPerronIntegral_halfInteger_moving_bound
  refine ⟨C, hC, fun m a T ha ha1 hT => ?_⟩
  let x : ℝ := (m : ℝ) + 1 / 2
  let b : ℝ := 1 + (Real.log x)⁻¹
  change 1 ≤ Real.log x → _
  intro hxlog
  have hx : 0 < x := by dsimp [x]; positivity
  have hb : 1 < b := lt_add_of_pos_right 1 (inv_pos.mpr (zero_lt_one.trans_le hxlog))
  have hshift := vonMangoldtPerronIntegral_shift_of_RH hRH x a b T hx ha ha1 hb hT
  let V := vonMangoldtPerronIntegral x a T
  let U := perronHorizontal (zetaPerronIntegrand x) a b T
  let L := perronHorizontal (zetaPerronIntegrand x) a b (-T)
  let E := vonMangoldtPerronIntegral x b T - 2 * (Real.pi : ℂ) * (chebyshevPsi x : ℂ)
  change vonMangoldtPerronIntegral x b T - 2 * (Real.pi : ℂ) * (x : ℂ) =
    V - Complex.I * (U - L) at hshift
  have hE : 2 * (Real.pi : ℂ) * ((chebyshevPsi x : ℂ) - (x : ℂ)) =
      -E + (V - Complex.I * (U - L)) := by
    rw [← hshift]
    dsimp only [E]
    ring
  have hEdges : ‖V - Complex.I * (U - L)‖ ≤ ‖V‖ + ‖U‖ + ‖L‖ := by
    calc
      _ ≤ ‖V‖ + ‖Complex.I * (U - L)‖ := norm_sub_le _ _
      _ = ‖V‖ + ‖U - L‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ _ := by rw [add_assoc]; exact add_le_add_left (norm_sub_le _ _) _
  rw [hE]
  exact (norm_add_le _ _).trans (by
    rw [norm_neg]
    exact add_le_add (htrunc m T hT hxlog) hEdges)

#print axioms perronRectangle_eq_zero
#print axioms perronVertical_inv_pos
#print axioms perronVertical_inv_neg
#print axioms perronHorizontal_inv_diff
#print axioms perronRectangle_inv
#print axioms perronRectangle_inv_sub_real
#print axioms zetaPerronRegularPart_analyticAt
#print axioms zetaPerronIntegrand_eq_regular_add
#print axioms perronRectangle_of_real_pole
#print axioms vonMangoldtPerronIntegral_shift
#print axioms vonMangoldtPerronIntegral_shift_of_RH
#print axioms chebyshevPsi_halfInteger_bound_of_RH
end RiemannResearch
