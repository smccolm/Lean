import Dubon2026.SourceGammaOneAnalyticPlaces
import Dubon2026.SourceGammaOneCurveGeometry
import Dubon2026.SourceCurveRationalResidueValues
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

/-! DUB-17/18 -> original finite Gamma1 Hecke-character realization ->
Picard-period comparison. Reuse actual rational residue evaluation on the
original integral-ratio field. Finite extension of the j-coordinate gives
closed residue fields; normalized analytic order proves that these actual
residue values are the analytic limits. No comparison map is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  (hT : ModularGroup.T ∈ Γ)

include hT

theorem analyticPlace_mem_iff (τ : ℍ) (f : functionFieldOver Γ ℂ) :
    f ∈ (analyticPlace hT τ).toValuationSubring ↔ 0 ≤ analyticOrder Γ τ f :=
  (exists_analytic_place hT τ).choose_spec.choose_spec.2.1 f

theorem realize_sub_constant_eventuallyEq
    (f : functionFieldOver Γ ℂ) (c : ℂ) (τ : ℍ) :
    (fun z : ℂ => realize Γ
      ((f - algebraMap ℂ (functionFieldOver Γ ℂ) c : functionFieldOver Γ ℂ) :
        LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z) - c := by
  have he : f - algebraMap ℂ (functionFieldOver Γ ℂ) c =
      f + algebraMap ℂ (functionFieldOver Γ ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [realize_add_eventuallyEq hT f
    (algebraMap ℂ (functionFieldOver Γ ℂ) (-c)) τ] with z hz
  have hconst : realize Γ
      ((algebraMap ℂ (functionFieldOver Γ ℂ) (-c) : functionFieldOver Γ ℂ) :
        LaurentSeries ℂ) (ofComplex z) = -c := realize_algebraMap hT (-c) (ofComplex z)
  simpa only [Pi.add_apply, hconst, sub_eq_add_neg] using hz

variable [Γ.FiniteIndex]

theorem place_residue_bijective (v : Place ℂ (functionFieldOver Γ ℂ)) :
    Function.Bijective (algebraMap ℂ v.ResidueField) := by
  letI := finiteDimensional_jCoordinateOver hT ℂ
  exact place_residue_bijective_of_finite_coordinate (jCoordinateOver Γ ℂ) v

/-- Actual residue evaluation on the original field, with zero at poles. -/
def placeEval (v : Place ℂ (functionFieldOver Γ ℂ)) (f : functionFieldOver Γ ℂ) : ℂ :=
  v.rationalEval (place_residue_bijective hT v) f

theorem realize_tendsto_residue (τ : ℍ) (f : functionFieldOver Γ ℂ)
    (hf : f ∈ (analyticPlace hT τ).toValuationSubring) :
    Tendsto (fun z : ℂ => realize Γ (f : LaurentSeries ℂ) (ofComplex z))
      (𝓝[≠] (τ : ℂ)) (𝓝 (placeEval hT (analyticPlace hT τ) f)) := by
  let v := analyticPlace hT τ
  let c := placeEval hT v f
  by_cases hc : f = algebraMap ℂ (functionFieldOver Γ ℂ) c
  · change Tendsto _ _ (𝓝 c)
    have he : (fun z : ℂ => realize Γ (f : LaurentSeries ℂ) (ofComplex z)) = fun _ => c := by
      funext z
      rw [hc]
      exact realize_algebraMap hT c (ofComplex z)
    rw [he]
    exact tendsto_const_nhds
  · have hne : f - algebraMap ℂ (functionFieldOver Γ ℂ) c ≠ 0 := sub_ne_zero.mpr hc
    have hz : v.rationalEval (place_residue_bijective hT v)
        (f - algebraMap ℂ (functionFieldOver Γ ℂ) c) = 0 := by
      rw [v.rationalEval_sub_algebraMap _ hf]
      exact sub_self c
    have ho := (v.rationalEval_eq_zero_iff_ord_pos (place_residue_bijective hT v)
      (sub_mem hf (v.algebraMap_mem' c)) hne).mp hz
    have hp : 0 < analyticOrder Γ τ
        (f - algebraMap ℂ (functionFieldOver Γ ℂ) c) := by
      rw [analyticPlace_order hT τ _ hne]
      exact WithTop.coe_pos.mpr (mul_pos
        (Int.natCast_pos.mpr (analyticRamification_pos hT τ)) ho)
    have hlim := (tendsto_zero_of_meromorphicOrderAt_pos hp).congr'
      (realize_sub_constant_eventuallyEq hT f c τ)
    have h := hlim.add_const c
    simpa only [sub_add_cancel, zero_add] using h

theorem regular_analytic_representative (τ : ℍ) (f : functionFieldOver Γ ℂ)
    (hf : f ∈ (analyticPlace hT τ).toValuationSubring) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      g τ = placeEval hT (analyticPlace hT τ) f ∧
      g =ᶠ[𝓝[≠] (τ : ℂ)] (fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z)) := by
  let F : ℂ → ℂ := fun z => realize Γ (f : LaurentSeries ℂ) (ofComplex z)
  have hm : MeromorphicAt F (τ : ℂ) := meromorphicAt_realize hT f τ
  let g := toMeromorphicNFAt F (τ : ℂ)
  have he : F =ᶠ[𝓝[≠] (τ : ℂ)] g := hm.eq_nhdsNE_toMeromorphicNFAt
  have ha : AnalyticAt ℂ g (τ : ℂ) := by
    apply meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [← meromorphicOrderAt_congr he]
    exact (analyticPlace_mem_iff hT τ f).mp hf
  refine ⟨g, ha, ?_, he.symm⟩
  exact tendsto_nhds_unique_of_eventuallyEq
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (realize_tendsto_residue hT τ f hf) he.symm

end
end Dubon2026.SourceFunctionField.GammaOne
