import Dubon2026.SourceGammaOneRationalAnalyticGerms
import Dubon2026.SourceGammaOneRealizationRestriction
import Dubon2026.SourceGammaOneHeckeBetaGerms
import Dubon2026.SourceGammaOneJRealization

/-! DUB-17/18 -> original Gamma1 norm reduction -> reverse-map diamond
comparison. Reuse the actual analytic realization and degeneracy germs in
upper-half-plane coordinates, where every matrix acts by a homeomorphism.
No analytic representative or field-action hypothesis is added. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem realize_restrict_upperHalfPlane_eventuallyEq {Γ Δ : Subgroup SL(2, ℤ)}
    (h : Δ ≤ Γ) (hT : ModularGroup.T ∈ Δ)
    (x : functionFieldOver Γ ℂ) (τ : ℍ) :
    realize Δ (x : LaurentSeries ℂ) =ᶠ[𝓝[≠] τ] realize Γ (x : LaurentSeries ℂ) :=
  SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp
    (realize_restrict_eventuallyEq h hT x τ)

theorem realize_smul_upperHalfPlane_eventuallyEq {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (x : functionFieldOver Γ ℂ) (γ : Γ) (τ : ℍ) :
    (fun z : ℍ => realize Γ (x : LaurentSeries ℂ) (γ.val • z))
      =ᶠ[𝓝[≠] τ] realize Γ (x : LaurentSeries ℂ) :=
  SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp
    (realize_smul_eventuallyEq hT x γ τ)

theorem realize_heckeBeta_upperHalfPlane_eventuallyEq (M d : ℕ) [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M)
    (hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M))
    (x : functionFieldOver (Gamma1 M) ℂ) (τ : ℍ) :
    realize (Gamma1 M ⊓ Gamma0 (d * M)) (heckeBeta ℂ M d x : LaurentSeries ℂ)
      =ᶠ[𝓝[≠] τ] fun z => realize (Gamma1 M) (x : LaurentSeries ℂ)
        (levelRaiseMatrix d • z) := by
  have ht : Tendsto ((↑) : ℍ → ℂ) (𝓝[≠] τ) (𝓝[≠] (τ : ℂ)) :=
    le_of_eq (SourceFunctionField.ModularRatios.map_coe_nhdsNE τ)
  have he := (realize_heckeBeta_eventuallyEq M d hT hH x τ).comp_tendsto ht
  filter_upwards [he] with z hz
  simpa only [Function.comp_apply, SourceFunctionField.ofComplex_dilation d z.im_pos,
    ofComplex_apply] using hz

theorem realize_adjacentJ_upperHalfPlane_eventuallyEq (M d : ℕ) [NeZero d]
    (hH : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ) :
    realize (Gamma1 M ⊓ Gamma0 (d * M)) (coeffEmb ℂ (qExpand ℚ d jq))
      =ᶠ[𝓝[≠] τ] fun z => JMultiplicity.jf (levelRaiseMatrix d • z) := by
  have hT : ModularGroup.T ∈ Gamma1 M := hH.1
  have hb : (heckeBeta ℂ M d (jCoordinateOver (Gamma1 M) ℂ) : LaurentSeries ℂ) =
      coeffEmb ℂ (qExpand ℚ d jq) := by
    rw [heckeBeta_coe]
    exact (coeffMap_qExpand (algebraMap ℚ ℂ) d jq).symm
  simpa only [hb, realize_jCoordinateOver hT] using
    realize_heckeBeta_upperHalfPlane_eventuallyEq M d hT hH
      (jCoordinateOver (Gamma1 M) ℂ) τ

end
end Dubon2026.SourceFunctionField.GammaOne
