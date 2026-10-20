/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourceEichlerPrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! The actual Eichler series equals its convergent vertical integral.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
actual period injectivity -> Eichler transformation law -> this integral identity.
Only the natural-power exponential moments and vertical q-parameter formula
needed for termwise integration are selected; broader exponential APIs are deferred.
-/

namespace Dubon2026
noncomputable section
open Complex Filter Function MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real Nat Topology Manifold
local notation "𝕢" => Function.Periodic.qParam

/-- Natural powers times an exponentially decaying factor are integrable on `(0, ∞)`. -/
private theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) le_rfl hb
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

/-- The integral of a natural power times an exponentially decaying factor on `(0, ∞)`. -/
private theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) = n.factorial / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Real.Gamma_nat_eq_factorial] at h
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast] at h
  have h' : ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) =
      (1 / a) ^ (n + 1) * n.factorial := by
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp
    rw [Real.rpow_natCast t n]
  rw [h', one_div, div_eq_mul_inv, inv_pow]
  ring

/-- Translation by `j` in the argument of `qParam` corresponds to multiplication by
`exp (-2 π I j / h)`. -/
private theorem sourceQParam_sub {h : ℝ} (z j : ℂ) : 𝕢 h (z - j) = 𝕢 h z * exp (-2 * π * I * j / h) := by
  simp only [Function.Periodic.qParam, ← Complex.exp_add]
  ring_nf

/-- Along the vertical ray from `z`, the powers of the local parameter acquire an exponential
factor: `𝕢 h (z + t I) ^ m = 𝕢 h z ^ m * e^{-2πmt/h}`. When `h > 0` and `m > 0`, this factor
decays exponentially as `t` increases. -/
private theorem sourceQParam_add_mul_I_pow {h : ℝ} (z : ℂ) (t : ℝ) (m : ℕ) :
    𝕢 h (z + t * I) ^ m = 𝕢 h z ^ m * (Real.exp (-(2 * π * m / h * t)) : ℂ) := by
  rw [← sub_neg_eq_add, sourceQParam_sub, mul_pow, ← Complex.exp_nat_mul, ofReal_exp]
  congr 2
  push_cast
  ring_nf
  rw [I_sq]
  ring

variable {h : ℝ} {f : ℍ → ℂ}

/-- The `m`-th term of the `q`-expansion of `f(z) (z - τ)ⁿ dz` along the vertical ray from `τ`,
with coefficient `A = aₘ 𝕢(τ)ᵐ`, is integrable. Its integral is `n! / (-2πi)ⁿ⁺¹` times the `m`-th
term `(h / m)ⁿ⁺¹ A` of the Eichler series, and its `L¹`-norm is `n! / (2π)ⁿ⁺¹` times the norm of
that term. -/
private lemma integrable_and_integral_rayTerm (hh : 0 < h) (n : ℕ) {m : ℕ} (hm : 0 < m) (A : ℂ) :
    Integrable (fun t : ℝ ↦ A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi (0 : ℝ), A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ) =
        n ! / (-2 * π * I) ^ (n + 1) * (((h : ℂ) / m) ^ (n + 1) * A) ∧
      ∫ t in Ioi (0 : ℝ),
          ‖A * I ^ (n + 1) * ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ)‖ =
        n ! / (2 * π) ^ (n + 1) * ‖((h : ℂ) / m) ^ (n + 1) * A‖ := by
  have hcm : 0 < 2 * π * m / h := div_pos (by positivity) hh
  have hint := integrableOn_pow_mul_exp_neg_mul_Ioi n hcm
  have hval := integral_pow_mul_exp_neg_mul_Ioi n hcm
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hh' : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh.ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨hint.ofReal.const_mul _, ?_, ?_⟩
  · rw [integral_const_mul, integral_complex_ofReal, hval]
    have hI : -2 * π * I * I = 2 * π := by
      rw [mul_assoc, I_mul_I]
      ring
    have hkey : ((h : ℂ) / m) ^ (n + 1) =
        ((-2 * π * I) ^ (n + 1) * I ^ (n + 1)) / (2 * π * m / h) ^ (n + 1) := by
      rw [← mul_pow, ← div_pow, hI]
      congr 1
      field_simp
    rw [hkey]
    push_cast
    field_simp
  · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t ↦ ‖A * I ^ (n + 1)‖ *
      (t ^ n * Real.exp (-(2 * π * m / h * t)))) fun t ht ↦ by
        rw [norm_mul (A * I ^ (n + 1)), norm_real,
          Real.norm_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt ht) n) (Real.exp_pos _).le)]]
    rw [integral_const_mul, hval]
    simp only [norm_mul, norm_pow, norm_div, norm_real, Complex.norm_natCast, norm_I, one_pow,
      mul_one, Real.norm_of_nonneg hh.le]
    have hmh : 2 * π * m / h * (h / m) = 2 * π := by
      field_simp [hh.ne', (Nat.cast_pos.mpr hm).ne']
    rw [← hmh, mul_pow]
    field_simp

/-- Along the vertical ray from `τ`, the integrand `f(z) (z - τ)ⁿ dz` is the sum of termwise
integrable functions whose `L¹`-norms are summable and whose integrals sum to
`n! / (-2πi)ⁿ⁺¹ · E_{n+1} f (τ)`. -/
private lemma exists_hasSum_integral_rayTerm (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (h₀ : (qExpansion h f).coeff 0 = 0)
    (n : ℕ) (τ : ℍ) :
    ∃ F : ℕ → ℝ → ℂ, (∀ m, Integrable (F m) (volume.restrict (Ioi 0))) ∧
      Summable (fun m ↦ ∫ t in Ioi (0 : ℝ), ‖F m t‖) ∧
      EqOn (fun t : ℝ ↦ f (ofComplex (τ + t * I)) * (t * I) ^ n * I) (fun t ↦ ∑' m, F m t)
        (Ioi 0) ∧
      HasSum (fun m ↦ ∫ t in Ioi (0 : ℝ), F m t)
        (n ! / (-2 * π * I) ^ (n + 1) * sourceEichlerIntegral h (n + 1) f τ) := by
  set a : ℕ → ℂ := fun m ↦ (qExpansion h f).coeff m
  -- The `m`-th term of the `q`-expansion of the integrand along the ray.
  set F : ℕ → ℝ → ℂ := fun m t ↦ a m * 𝕢 h τ ^ m * I ^ (n + 1) *
    ((t ^ n * Real.exp (-(2 * π * m / h * t)) : ℝ) : ℂ)
  -- The terms of the Eichler series.
  set E : ℕ → ℂ := fun m ↦ ((h : ℂ) / m) ^ (n + 1) * (a m * 𝕢 h τ ^ m)
  have hE : HasSum E (sourceEichlerIntegral h (n + 1) f τ) := by
    simpa only [E, mul_assoc] using hasSum_sourceEichlerIntegral hh hfper hfhol hfbdd (n + 1) τ
  have hF (m : ℕ) : Integrable (F m) (volume.restrict (Ioi 0)) ∧
      ∫ t in Ioi (0 : ℝ), F m t = n ! / (-2 * π * I) ^ (n + 1) * E m ∧
      ∫ t in Ioi (0 : ℝ), ‖F m t‖ = n ! / (2 * π) ^ (n + 1) * ‖E m‖ := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, E, a, h₀]
    · exact integrable_and_integral_rayTerm hh n hm _
  refine ⟨F, fun m ↦ (hF m).1, by simpa only [(hF _).2.2] using hE.summable.norm.mul_left _,
    fun t ht ↦ ?_, by simpa only [(hF _).2.1] using hE.mul_left _⟩
  -- Along the ray, the integrand is the sum of the `F m`.
  have him : 0 < (τ + t * I : ℂ).im := by simpa using add_pos τ.im_pos ht
  have hq := (hasSum_qExpansion hh hfper hfhol hfbdd (ofComplex (τ + t * I))).mul_right
    ((t * I) ^ n * I)
  rw [← mul_assoc] at hq
  refine (hq.tsum_eq.symm.trans (tsum_congr fun m ↦ ?_))
  simp only [ofComplex_apply_of_im_pos him, smul_eq_mul, sourceQParam_add_mul_I_pow, F,
    a]
  push_cast
  ring

/-- If `f` is holomorphic, `h`-periodic and bounded at `i∞` with vanishing constant term `a₀`,
then the period integrand `f(z) (z - τ)ⁿ dz` is integrable along the vertical ray `z = τ + i t`,
`t > 0`. -/
theorem integrableOn_eichlerIntegrand (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (h₀ : (qExpansion h f).coeff 0 = 0)
    (n : ℕ) (τ : ℍ) :
    IntegrableOn (fun t : ℝ ↦ f (ofComplex (τ + t * I)) * (t * I) ^ n * I) (Ioi 0) := by
  obtain ⟨F, hint, hsum, heq, -⟩ :=
    exists_hasSum_integral_rayTerm hh hfper hfhol hfbdd h₀ n τ
  have hcont : ContinuousOn (fun t : ℝ ↦ f (ofComplex (τ + t * I)) * (t * I) ^ n * I) (Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) continuousOn_const
    exact (UpperHalfPlane.mdifferentiable_iff.mp hfhol).continuousOn.comp (f := fun t : ℝ ↦
      (τ : ℂ) + t * I) (by fun_prop) fun t ht ↦ by simpa using add_pos τ.im_pos ht
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioi, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ t in Ioi (0 : ℝ), ‖f (ofComplex (τ + t * I)) * (t * I) ^ n * I‖ₑ
      ≤ ∫⁻ t in Ioi 0, ∑' m, ‖F m t‖ₑ :=
        setLIntegral_mono' measurableSet_Ioi fun t ht ↦
          (congrArg enorm (heq ht)).trans_le enorm_tsum_le_tsum_enorm
    _ = ∑' m, ∫⁻ t in Ioi 0, ‖F m t‖ₑ :=
        lintegral_tsum fun m ↦ (hint m).aestronglyMeasurable.enorm
    _ = ENNReal.ofReal (∑' m, ∫ t in Ioi (0 : ℝ), ‖F m t‖) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun m ↦ integral_nonneg fun t ↦ norm_nonneg _) hsum]
        simp only [ofReal_integral_norm_eq_lintegral_enorm (hint _)]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **The Eichler integral as an integral**: if `f` is holomorphic, `h`-periodic and bounded at
`i∞` with vanishing constant term `a₀`, then

`E_{n+1} f (τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`,

the integral taken along the vertical ray `z = τ + i t`, `t > 0`. The integrand is integrable by
`integrableOn_eichlerIntegrand`. -/
theorem sourceEichlerIntegral_eq_integral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (h₀ : (qExpansion h f).coeff 0 = 0)
    (n : ℕ) (τ : ℍ) :
    sourceEichlerIntegral h (n + 1) f τ = (-2 * π * I) ^ (n + 1) / n ! *
      ∫ t in Ioi (0 : ℝ), f (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
  obtain ⟨F, hint, hsum, heq, hval⟩ :=
    exists_hasSum_integral_rayTerm hh hfper hfhol hfbdd h₀ n τ
  have hc : (n ! : ℂ) / (-2 * π * I) ^ (n + 1) ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
      (pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    (hasSum_integral_of_summable_integral_norm hint hsum).unique hval, ← mul_assoc, ← inv_div,
    inv_mul_cancel₀ hc, one_mul]

/-- For a cusp form `f`, the period integrand `f(z) (z - τ)ⁿ dz` is integrable along the vertical
ray `z = τ + i t`, `t > 0`. -/
theorem sourceCuspForm_integrableOn_eichlerIntegrand {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) (τ : ℍ) :
    IntegrableOn (fun t : ℝ ↦ f (ofComplex (τ + t * I)) * (t * I) ^ n * I) (Ioi 0) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  exact integrableOn_eichlerIntegrand hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (_root_.CuspFormClass.qExpansion_coeff_zero f hh hΓ) n τ

/-- **The Eichler integral of a cusp form as an integral**: for a cusp form `f`,

`E_{n+1} f (τ) = (-2πi)ⁿ⁺¹ / n! · ∫_τ^{i∞} f(z) (z - τ)ⁿ dz`,

the integral taken along the vertical ray `z = τ + i t`, `t > 0`. For a cusp form of weight
`k ≥ 2` and `n = k - 2`, this is the classical integral formula for its Eichler integral. -/
theorem sourceCuspForm_eichlerIntegral_eq_integral {F : Type*} [FunLike F ℍ ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) (τ : ℍ) :
    sourceEichlerIntegral h (n + 1) f τ = (-2 * π * I) ^ (n + 1) / n ! *
      ∫ t in Ioi (0 : ℝ), f (ofComplex (τ + t * I)) * (t * I) ^ n * I := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  exact sourceEichlerIntegral_eq_integral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) (_root_.CuspFormClass.qExpansion_coeff_zero f hh hΓ) n τ

end
end Dubon2026
