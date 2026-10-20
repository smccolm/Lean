/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-! The iterated antiderivative required by injectivity of the actual period map.
Selected from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
actual period injectivity -> Eichler integral vanishing and derivative recovery.
Pinned Mathlib already supplies the q-expansion convergence, negative-weight
vanishing, and weight-zero constancy. Incidental linearity and coefficient
identification lemmas of the external Eichler API are deferred.
-/

namespace Dubon2026
noncomputable section
open Complex Filter Function
open UpperHalfPlane hiding I
open scoped Real Topology Manifold Derivative
local notation "𝕢" => Function.Periodic.qParam

/-- The actual Fourier parameter has its usual complex derivative. -/
theorem sourceHasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (𝕢 h z * (2 * π * I / h)) z := by
  simpa only [Function.Periodic.qParam, id_eq, mul_one] using
    (((hasDerivAt_id z).const_mul (2 * (π : ℂ) * I)).div_const h).cexp

variable {h : ℝ} {f : ℍ → ℂ}

/-- The `n`-fold **Eichler integral** of `f : ℍ → ℂ` at width `h`: the series
`∑ (h / m)ⁿ aₘ qᵐ`, where `aₘ` are the coefficients of `qExpansion h f` and `q = 𝕢 h τ`.
It is the termwise `n`-fold antiderivative of the `q`-expansion of `f` for the normalized
derivative `D = (2πi)⁻¹ d/dτ`, with the constant term dropped when `n ≥ 1`. For a cusp form of
weight `k ≥ 2`, `sourceEichlerIntegral h (k - 1) f` is the classical Eichler integral of `f`. -/
def sourceEichlerIntegral (h : ℝ) (n : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m

/-- A term of the Eichler series is bounded by `hⁿ` times the corresponding term of the
`q`-expansion: the rescaling factor `h / m` has norm at most `h` (it is `0` at `m = 0`). -/
private lemma norm_eichlerTerm_le (hh : 0 < h) (n m : ℕ) (a q : ℂ) :
    ‖((h : ℂ) / m) ^ n * a * q ^ m‖ ≤ h ^ n * (‖a‖ * ‖q‖ ^ m) := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow, ← mul_assoc]
  gcongr
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hh.le]
  · rw [norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hh.le]
    exact div_le_self hh.le (by exact_mod_cast hm)

/-- **The defining series of the Eichler integral converges** at every point of `ℍ`. -/
theorem hasSum_sourceEichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m)
      (sourceEichlerIntegral h n f τ) := by
  have hs := (hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (q := (‖𝕢 h τ‖ : ℂ))
    (by simpa using (Periodic.norm_qParam_lt_iff hh 0 τ).mpr τ.im_pos)).summable.norm
  simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hs
  exact (Summable.of_norm_bounded (hs.mul_left (h ^ n))
    fun m ↦ norm_eichlerTerm_le hh n m _ _).hasSum

/-- On a half-plane `ε < im w` the terms of the Eichler series are dominated by a summable
sequence independent of `w`. -/
private lemma norm_eichlerTerm_le_of_lt_im (hh : 0 < h) (n m : ℕ) (a : ℂ) {ε : ℝ} {w : ℂ}
    (hw : ε < w.im) :
    ‖((h : ℂ) / m) ^ n * a * 𝕢 h w ^ m‖ ≤ h ^ n * (‖a‖ * Real.exp (-2 * π * ε / h) ^ m) := by
  refine (norm_eichlerTerm_le hh n m a _).trans ?_
  gcongr
  exact ((Periodic.norm_qParam_lt_iff hh ε w).mpr hw).le

/-- The Eichler series, as a function on `ℂ`, is differentiable on the upper half-plane, and its
derivative is the termwise derivative. -/
private lemma eichlerSeries_hasSum_deriv (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ
        (fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m) z ∧
      HasSum (fun m : ℕ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m *
          (2 * π * I * m / h * 𝕢 h z ^ m))
        (deriv (fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m *
          𝕢 h w ^ m) z) := by
  set ε := z.im / 2
  have hε : 0 < ε := half_pos hz
  have hU : IsOpen {w : ℂ | ε < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ {w : ℂ | ε < w.im} := half_lt_self hz
  have hr : Real.exp (-2 * π * ε / h) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hh)
  have hu := (hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (q := (Real.exp (-2 * π * ε / h) : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      using hr)).summable.norm
  simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at hu
  have hu := hu.mul_left (h ^ n)
  have hdiff (m : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ ↦ ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m)
      {w : ℂ | ε < w.im} :=
    ((Periodic.differentiable_qParam.pow m).const_mul _).differentiableOn
  have hle (m : ℕ) (w : ℂ) (hw : w ∈ {w : ℂ | ε < w.im}) :=
    norm_eichlerTerm_le_of_lt_im hh n m ((qExpansion h f).coeff m) hw
  refine ⟨(differentiableOn_tsum_of_summable_norm hu hdiff hU hle).differentiableAt
    (hU.mem_nhds hzU), ?_⟩
  convert hasSum_deriv_of_summable_norm hu hdiff hU hle hzU using 2 with m
  have hpow : HasDerivAt (fun w ↦ 𝕢 h w ^ m) (2 * π * I * m / h * 𝕢 h z ^ m) z := by
    convert (sourceHasDerivAt_qParam h z).pow m using 1
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      push_cast
      ring
  exact ((hpow.const_mul _).deriv).symm

/-- The Eichler integral, read on `ℂ` through `ofComplex`, agrees with its defining series near
every point of the upper half-plane. -/
private lemma sourceEichlerIntegral_comp_ofComplex_eventuallyEq (n : ℕ) (τ : ℍ) :
    sourceEichlerIntegral h n f ∘ ofComplex =ᶠ[𝓝 (τ : ℂ)]
      fun w : ℂ ↦ ∑' m : ℕ, ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h w ^ m := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
  simp [sourceEichlerIntegral, ofComplex_apply_of_im_pos hw]

/-- **The Eichler integral is holomorphic** on `ℍ`. -/
theorem mdifferentiable_sourceEichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) :
    MDiff (sourceEichlerIntegral h n f) := fun τ ↦
  mdifferentiableAt_iff.mpr <| (eichlerSeries_hasSum_deriv hh hfper hfhol hfbdd n
    τ.im_pos).1.congr_of_eventuallyEq (sourceEichlerIntegral_comp_ofComplex_eventuallyEq n τ)

/-- **The Eichler integral vanishes at `i∞`** once at least one antiderivative is taken: its
`q`-expansion has no constant term. -/
theorem isZeroAtImInfty_sourceEichlerIntegral (hh : 0 < h) (hfper : Periodic (f ∘ ofComplex) h)
    (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) (n : ℕ) :
    IsZeroAtImInfty (sourceEichlerIntegral h (n + 1) f) := by
  have hr : Real.exp (-2 * π / h) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hh)
  have hs := (hasSum_qExpansion_of_norm_lt hh hfper hfhol hfbdd
    (q := (Real.exp (-2 * π / h) : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      using hr)).summable.norm
  simp only [norm_smul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le] at hs
  have hlim := tendsto_tsum_of_dominated_convergence
    (𝓕 := atImInfty)
    (f := fun τ : ℍ => fun m : ℕ =>
      ((h : ℂ) / m) ^ (n + 1) * (qExpansion h f).coeff m * 𝕢 h τ ^ m)
    (g := fun _ : ℕ => (0 : ℂ)) (hs.mul_left (h ^ (n + 1)))
    (fun m => by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa only [Nat.cast_zero, div_zero, zero_pow (Nat.succ_ne_zero n), zero_mul] using
          (tendsto_const_nhds : Tendsto (fun _ : ℍ => (0 : ℂ)) atImInfty (𝓝 0))
      · simpa [zero_pow hm.ne'] using
          ((qParam_tendsto_atImInfty hh).pow m).const_mul
            (((h : ℂ) / m) ^ (n + 1) * (qExpansion h f).coeff m))
    (by
      have hgt : ∀ᶠ τ : ℍ in atImInfty, 1 < τ.im :=
        (atImInfty_mem _).mpr ⟨2, fun _ hτ => lt_of_lt_of_le (by norm_num) hτ⟩
      filter_upwards [hgt] with τ hτ
      intro m
      simpa only [mul_one] using
        norm_eichlerTerm_le_of_lt_im hh (n + 1) m ((qExpansion h f).coeff m) hτ)
  simpa only [sourceEichlerIntegral, tsum_apply, tsum_zero] using hlim

/-- The normalized derivative acts on the Eichler series termwise, as multiplication of the
`m`-th term by `m / h`. -/
private lemma hasSum_normalizedDerivOfComplex_sourceEichlerIntegral (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) (τ : ℍ) :
    HasSum (fun m : ℕ ↦ (m / h) * ((h : ℂ) / m) ^ n * (qExpansion h f).coeff m * 𝕢 h τ ^ m)
      (D (sourceEichlerIntegral h n f) τ) := by
  rw [Derivative.normalizedDerivOfComplex,
    (sourceEichlerIntegral_comp_ofComplex_eventuallyEq n τ).deriv_eq]
  convert (eichlerSeries_hasSum_deriv hh hfper hfhol hfbdd n τ.im_pos).2.mul_left
    (2 * π * I)⁻¹ using 2 with m
  field_simp

/-- The rescaling factors of consecutive Eichler integrals differ by the factor `m / h` that
`D` produces, away from the constant term. -/
private lemma natCast_div_mul_div_natCast_pow_succ (hh : h ≠ 0) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (m / h) * ((h : ℂ) / m) ^ (n + 1) = ((h : ℂ) / m) ^ n := by
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [pow_succ]
  field_simp

/-- **Differentiating an Eichler integral of order at least two** lowers the order by one:
`D E_{n+2} f = E_{n+1} f`. -/
theorem normalizedDerivOfComplex_sourceEichlerIntegral_add_two (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) : D (sourceEichlerIntegral h (n + 2) f) = sourceEichlerIntegral h (n + 1) f := by
  funext τ
  refine (hasSum_normalizedDerivOfComplex_sourceEichlerIntegral hh hfper hfhol hfbdd (n + 2) τ).unique ?_
  convert hasSum_sourceEichlerIntegral hh hfper hfhol hfbdd (n + 1) τ using 2 with m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [natCast_div_mul_div_natCast_pow_succ hh.ne' hm]

/-- **Differentiating the first Eichler integral** returns the function minus its constant term:
`D E_1 f = f - a₀`. -/
theorem normalizedDerivOfComplex_sourceEichlerIntegral_one (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f) :
    D (sourceEichlerIntegral h 1 f) = fun τ ↦ f τ - (qExpansion h f).coeff 0 := by
  funext τ
  refine (hasSum_normalizedDerivOfComplex_sourceEichlerIntegral hh hfper hfhol hfbdd 1 τ).unique ?_
  convert (hasSum_qExpansion hh hfper hfhol hfbdd τ).sub
    (hasSum_ite_eq 0 ((qExpansion h f).coeff 0)) using 2 with m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [natCast_div_mul_div_natCast_pow_succ hh.ne' hm]
    simp [hm]

/-- **The Eichler integral is an iterated antiderivative**: differentiating `E_{n+1} f` exactly
`n + 1` times with the normalized derivative `D` returns `f` minus its constant term. -/
theorem iterate_normalizedDerivOfComplex_sourceEichlerIntegral (hh : 0 < h)
    (hfper : Periodic (f ∘ ofComplex) h) (hfhol : MDiff f) (hfbdd : IsBoundedAtImInfty f)
    (n : ℕ) :
    D^[n + 1] (sourceEichlerIntegral h (n + 1) f) = fun τ ↦ f τ - (qExpansion h f).coeff 0 := by
  induction n with
  | zero => exact normalizedDerivOfComplex_sourceEichlerIntegral_one hh hfper hfhol hfbdd
  | succ n ih =>
    rw [iterate_succ_apply, normalizedDerivOfComplex_sourceEichlerIntegral_add_two hh hfper hfhol hfbdd,
      ih]

/-- **The Eichler integral of a cusp form is an iterated antiderivative**:
`D^{n+1} E_{n+1} f = f`. For a cusp form of weight `k ≥ 2` and `n + 1 = k - 1`, this recovers `f`
from its Eichler integral. -/
theorem sourceCuspForm_iterate_normalizedDerivOfComplex_eichlerIntegral {F : Type*}
    [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [CuspFormClass F Γ k] (f : F)
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (n : ℕ) :
    D^[n + 1] (sourceEichlerIntegral h (n + 1) f) = f := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  rw [iterate_normalizedDerivOfComplex_sourceEichlerIntegral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f), _root_.CuspFormClass.qExpansion_coeff_zero f hh hΓ]
  simp

end
end Dubon2026
