import Dubon2026.SourceModularProjectiveFibers
import Dubon2026.SourceModularSmoothedFundamental

/-! The source central-sign normalization for the smooth modular partition.
DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic
reciprocity -> invariant integral limit. Existing finite orbit support
and the proved two-element projection fibers derive projective mass 1/2.
Native measurable infinite sums avoid redoing the source ENNReal conversion. -/
namespace Dubon2026.SourceSmoothedUnfolding
noncomputable section
open UpperHalfPlane MeasureTheory Filter Set SourceSmoothedFundamental
open scoped MatrixGroups Topology ENNReal
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

theorem finite_support_projective (T : ℝ) (τ : ℍ) :
    (Function.support fun g : projectiveIntegralSubgroup Γ =>
      smoothedFundamental Γ T ((g • τ : ℍ) : ℂ)).Finite := by
  refine ((finite_support_smul Γ T τ).image (projection Γ)).subset ?_
  intro g hg
  obtain ⟨a, rfl⟩ := projection_surjective Γ g
  exact ⟨a, hg, rfl⟩

/-- Orbit sum over the faithful projective subgroup, with exact central multiplicity. -/
def projectiveMass (T : ℝ) (τ : ℍ) : ℝ :=
  ∑' g : projectiveIntegralSubgroup Γ, smoothedFundamental Γ T ((g • τ : ℍ) : ℂ)

omit [Γ.FiniteIndex] in
theorem projectiveMass_nonneg (T : ℝ) (τ : ℍ) : 0 ≤ projectiveMass Γ T τ :=
  tsum_nonneg fun _ => smoothedFundamental_nonneg Γ T _

theorem two_mul_projectiveMass (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (T : ℝ) (τ : ℍ) :
    2 * projectiveMass Γ T τ =
      ∑ᶠ a : Γ, smoothedFundamental Γ T (((a : SL(2, ℤ)) • τ : ℍ) : ℂ) := by
  have hs := summable_of_hasFiniteSupport (L := SummationFilter.unconditional _) (finite_support_smul Γ T τ)
  have hp := summable_of_hasFiniteSupport (L := SummationFilter.unconditional _) (finite_support_projective Γ T τ)
  have he := tsum_projection Γ hΓ (fun g =>
    ENNReal.ofReal (smoothedFundamental Γ T ((g • τ : ℍ) : ℂ)))
  change (∑' a : Γ, ENNReal.ofReal
    (smoothedFundamental Γ T (((a : SL(2, ℤ)) • τ : ℍ) : ℂ))) = _ at he
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => smoothedFundamental_nonneg Γ T _) hs,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => smoothedFundamental_nonneg Γ T _) hp,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at he
  have hr := (ENNReal.ofReal_eq_ofReal_iff
    (tsum_nonneg fun _ => smoothedFundamental_nonneg Γ T _)
    (mul_nonneg (by norm_num) (projectiveMass_nonneg Γ T τ))).mp he
  rw [tsum_eq_finsum (finite_support_smul Γ T τ)] at hr
  exact hr.symm

theorem projectiveMass_le_half (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (T : ℝ) (τ : ℍ) :
    projectiveMass Γ T τ ≤ 1 / 2 := by
  have h := finsum_smul_le_one Γ T τ
  rw [← two_mul_projectiveMass Γ hΓ T τ] at h
  linarith

theorem projectiveMass_eq_half (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {T : ℝ} {τ : ℍ}
    (hτ : max τ.im τ.im⁻¹ ≤ T) : projectiveMass Γ T τ = 1 / 2 := by
  have h := finsum_smul_eq_one Γ T hτ
  rw [← two_mul_projectiveMass Γ hΓ T τ] at h
  linarith

theorem tendsto_projectiveMass (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (τ : ℍ) :
    Tendsto (fun T : ℝ => projectiveMass Γ T τ) atTop (𝓝 (1 / 2)) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop (max τ.im τ.im⁻¹)] with T hT
    exact (projectiveMass_eq_half Γ hΓ hT).symm)

theorem measurable_projectiveMass (T : ℝ) : Measurable (projectiveMass Γ T) := by
  apply Measurable.tsum
  intro g
  exact ((SourceSmoothedFundamental.contDiff Γ T 0).continuous.measurable.comp
    (continuous_coe.measurable.comp (measurable_const_smul g)))

end
end Dubon2026.SourceSmoothedUnfolding
