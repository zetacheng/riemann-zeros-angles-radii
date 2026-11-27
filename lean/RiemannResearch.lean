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
