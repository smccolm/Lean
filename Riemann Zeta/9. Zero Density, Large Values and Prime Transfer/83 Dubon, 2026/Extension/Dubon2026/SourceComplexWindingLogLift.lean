import Mathlib

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> winding-period
comparison -> logarithm of the nonvanishing invariant quotient.
Native exponential covering and lift uniqueness are reused. All smoothness,
derivatives, integer character and cusp conditions are proved from the actual
function; no logarithm or parabolic-character certificate is assumed. -/
namespace Dubon2026.SourceWindingLog
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Topology
open scoped MatrixGroups Topology Real

theorem eq_zero_of_exp_eq_one_of_norm_lt {D : ℂ} (h1 : exp D = 1) (h2 : ‖D‖ < 2 * π) : D = 0 := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  rw [hk] at h2 ⊢
  have hnorm : ‖(k : ℂ) * (2 * π * I)‖ = |(k : ℝ)| * (2 * π) := by
    rw [norm_mul, Complex.norm_intCast]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  rw [hnorm] at h2
  have hk0 : |(k : ℝ)| < 1 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  have : k = 0 := by
    have h' : |(k : ℤ)| < 1 := by exact_mod_cast hk0
    exact Int.abs_lt_one_iff.1 h'
  simp [this]

theorem apply_eq_of_exp_eq_one {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {D : X → ℂ} (hD : Continuous D) (h1 : ∀ x, exp (D x) = 1) (x y : X) : D x = D y := by
  exact Complex.isCoveringMap_exp.const_of_comp hD (fun a b => by
    apply Subtype.ext
    exact (h1 a).trans (h1 b).symm) x y


section Lift

variable (Φ : ℂ → ℂ) (hΦc : ∀ τ : ℍ, ContinuousAt Φ τ) (hne : ∀ τ : ℍ, Φ τ ≠ 0)
include hΦc hne

/-- The actual nonvanishing function as a continuous map to punctured C. -/
def toUnits : C(ℍ, {z : ℂ // z ≠ 0}) where
  toFun τ := ⟨Φ τ, hne τ⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_iff_continuousAt.2 fun τ => (hΦc τ).comp continuous_coe.continuousAt

theorem exists_lift : ∃ L₀ : C(ℍ, ℂ), ∀ τ : ℍ, exp (L₀ τ) = Φ τ := by
  have he : (⟨exp (log (Φ UpperHalfPlane.I)), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) =
      toUnits Φ hΦc hne UpperHalfPlane.I := by
    apply Subtype.ext
    show exp (log (Φ _)) = Φ _
    exact Complex.exp_log (hne _)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (toUnits Φ hΦc hne) UpperHalfPlane.I (log (Φ UpperHalfPlane.I)) he
  refine ⟨F, fun τ => ?_⟩
  have := congrFun hF τ
  simp only [Function.comp] at this
  exact congrArg Subtype.val this

end Lift

section Local

variable {Φ L : ℂ → ℂ} {τ : ℍ}

theorem eventuallyEq_log (hΦ : ContinuousAt Φ (τ : ℂ)) (hne : Φ τ ≠ 0)
    (hLc : ContinuousAt L (τ : ℂ)) (hexp : ∀ᶠ z in 𝓝 (τ : ℂ), exp (L z) = Φ z) :
    L =ᶠ[𝓝 (τ : ℂ)] fun z => L τ + log (Φ z * (Φ τ)⁻¹) := by
  set ℓ : ℂ → ℂ := fun z => log (Φ z * (Φ τ)⁻¹) with hℓ
  have hℓτ : ℓ τ = 0 := by simp [hℓ, mul_inv_cancel₀ hne]
  have hℓc : ContinuousAt ℓ (τ : ℂ) := by
    have h1 : ContinuousAt (fun z => Φ z * (Φ τ)⁻¹) (τ : ℂ) := hΦ.mul continuousAt_const
    have h2 : ContinuousAt log (Φ τ * (Φ τ)⁻¹) := by
      rw [mul_inv_cancel₀ hne]; exact continuousAt_clog Complex.one_mem_slitPlane
    exact ContinuousAt.comp (f := fun z => Φ z * (Φ τ)⁻¹) (x := (τ : ℂ)) h2 h1
  have hΦne : ∀ᶠ z in 𝓝 (τ : ℂ), Φ z ≠ 0 := hΦ.eventually_ne hne
  have hLsmall : ∀ᶠ z in 𝓝 (τ : ℂ), ‖L z - L τ‖ < 1 := by
    have := (hLc.sub_const (L τ)).norm
    have h0 : ‖L (τ : ℂ) - L τ‖ < 1 := by simp
    exact this.eventually (gt_mem_nhds h0)
  have hℓsmall : ∀ᶠ z in 𝓝 (τ : ℂ), ‖ℓ z‖ < 1 := by
    have := hℓc.norm
    have h0 : ‖ℓ (τ : ℂ)‖ < 1 := by rw [hℓτ]; simp
    exact this.eventually (gt_mem_nhds h0)
  filter_upwards [hexp, hΦne, hLsmall, hℓsmall] with z hz hz0 h1 h2
  have hexpℓ : exp (ℓ z) = Φ z * (Φ τ)⁻¹ := Complex.exp_log (mul_ne_zero hz0 (inv_ne_zero hne))
  have hexpτ : exp (L τ) = Φ τ := hexp.self_of_nhds
  have hone : exp (L z - L τ - ℓ z) = 1 := by
    rw [Complex.exp_sub, Complex.exp_sub, hz, hexpτ, hexpℓ]
    field_simp
  have hnorm : ‖L z - L τ - ℓ z‖ < 2 * π := by
    calc ‖L z - L τ - ℓ z‖ ≤ ‖L z - L τ‖ + ‖ℓ z‖ := norm_sub_le _ _
      _ < 1 + 1 := add_lt_add h1 h2
      _ ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have := eq_zero_of_exp_eq_one_of_norm_lt hone hnorm
  show L z = L τ + ℓ z
  linear_combination this

theorem contDiffAt_log_lift (hΦ : ContDiffAt ℝ 1 Φ (τ : ℂ)) (hne : Φ τ ≠ 0)
    (hLc : ContinuousAt L (τ : ℂ)) (hexp : ∀ᶠ z in 𝓝 (τ : ℂ), exp (L z) = Φ z) :
    ContDiffAt ℝ 1 L (τ : ℂ) := by
  have hev := eventuallyEq_log hΦ.continuousAt hne hLc hexp
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  refine contDiffAt_const.add ?_
  have h1 : ContDiffAt ℝ 1 (fun z => Φ z * (Φ τ)⁻¹) (τ : ℂ) := hΦ.mul contDiffAt_const
  have h2 : ContDiffAt ℝ 1 log (Φ τ * (Φ τ)⁻¹) := by
    rw [mul_inv_cancel₀ hne]
    exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
  exact ContDiffAt.comp (f := fun z => Φ z * (Φ τ)⁻¹) (τ : ℂ) h2 h1

theorem hasFDerivAt_log_lift (hΦ : ContDiffAt ℝ 1 Φ (τ : ℂ)) (hne : Φ τ ≠ 0)
    (hLc : ContinuousAt L (τ : ℂ)) (hexp : ∀ᶠ z in 𝓝 (τ : ℂ), exp (L z) = Φ z) :
    HasFDerivAt L ((Φ τ)⁻¹ • fderiv ℝ Φ τ) (τ : ℂ) := by
  have hLd : DifferentiableAt ℝ L (τ : ℂ) :=
    (contDiffAt_log_lift hΦ hne hLc hexp).differentiableAt (by norm_num)

  have hcomp : HasFDerivAt (fun z => exp (L z)) (exp (L τ) • fderiv ℝ L τ) (τ : ℂ) :=
    (Complex.hasDerivAt_exp (L τ)).comp_hasFDerivAt (τ : ℂ) hLd.hasFDerivAt
  have hΦd : HasFDerivAt Φ (exp (L τ) • fderiv ℝ L τ) (τ : ℂ) := hcomp.congr_of_eventuallyEq (by
    filter_upwards [hexp] with z hz using hz.symm)
  have hexpτ : exp (L τ) = Φ τ := hexp.self_of_nhds
  have hfd : fderiv ℝ Φ τ = Φ τ • fderiv ℝ L τ := by rw [hΦd.fderiv, hexpτ]
  have : (Φ τ)⁻¹ • fderiv ℝ Φ τ = fderiv ℝ L τ := by
    rw [hfd, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [this]
  exact hLd.hasFDerivAt

end Local

end
end Dubon2026.SourceWindingLog
