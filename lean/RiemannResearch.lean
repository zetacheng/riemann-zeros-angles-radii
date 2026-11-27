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

/-- The forward direction of the v16 one-sided criterion at q = 1:
a one-sided bound at exponent θ excludes every zeta zero to its right. -/
theorem riemannZeta_ne_zero_of_oneSidedBound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 1)
    (h : OneSidedBound θ) (ρ : ℂ) (hρ : θ < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hzero
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
    have he := adjustedPrimeError_mellin_continuation C θ θ hθ.le hθ.le F hF hinit z hz hz0 hzθ hUz
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
