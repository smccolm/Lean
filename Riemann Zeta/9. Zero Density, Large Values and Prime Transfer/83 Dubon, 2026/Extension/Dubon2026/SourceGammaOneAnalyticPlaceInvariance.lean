import Dubon2026.SourceGammaOneAnalyticResidues
import Dubon2026.SourceOriginalAnalyticPlaceInvariance

/-! DUB-17/18 -> original Gamma1 Picard-period comparison -> global charts.
Reuse the proved local Gamma0 argument on the actual Gamma integral-ratio
field. Equal weights cancel in the quotient germ; the native Mobius order
identity identifies the actual normalized places on subgroup orbits.
SourceOriginalAnalyticPlaceInvariance credits anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_complexPlaceDictionary. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem realize_smul_eventuallyEq {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (γ : Γ) (τ : ℍ) :
    (fun z : ℂ => realize Γ (x : LaurentSeries ℂ)
      (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨k, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  filter_upwards [ModularRatios.eventually_ne_zero_ofComplex h hh τ] with z hz
  have hsm : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • ofComplex z = (γ : SL(2, ℤ)) • ofComplex z := by
    simp
  have hhγ : h ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ k * h (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' h γ.2 _
  have hgγ : g ((γ : SL(2, ℤ)) • ofComplex z) =
      denom (γ : SL(2, ℤ)) (ofComplex z) ^ k * g (ofComplex z) :=
    SlashInvariantForm.slash_action_eqn_SL'' g γ.2 _
  have hd : (denom (γ : SL(2, ℤ)) (ofComplex z) : ℂ) ^ k ≠ 0 :=
    zpow_ne_zero _ (denom_ne_zero _ _)
  have hne : h ((γ : SL(2, ℤ)) • ofComplex z) ≠ 0 := by
    rw [hhγ]
    exact mul_ne_zero hd hz
  rw [hsm, realize_eq_div Γ hT g h x hx _ hne, realize_eq_div Γ hT g h x hx _ hz,
    hgγ, hhγ, mul_div_mul_left _ _ hd]

theorem analyticOrder_smul {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ)
    (γ : Γ) (τ : ℍ) (x : functionFieldOver Γ ℂ) :
    analyticOrder Γ ((γ : SL(2, ℤ)) • τ) x = analyticOrder Γ τ x := by
  unfold analyticOrder
  have hdet1 : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hdet : 0 < (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det := by rw [hdet1]; exact one_pos
  rw [show ((((γ : SL(2, ℤ)) • τ : ℍ)) : ℂ) = ↑((((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul hdet]
  exact meromorphicOrderAt_congr (realize_smul_eventuallyEq hT x γ τ)

theorem analyticPlace_smul {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ)
    (γ : Γ) (τ : ℍ) :
    analyticPlace hT ((γ : SL(2, ℤ)) • τ) = analyticPlace hT τ := by
  apply SourceCurve.Place.ext
  apply SetLike.ext
  intro x
  rw [analyticPlace_mem_iff, analyticPlace_mem_iff]
  rw [analyticOrder_smul hT]

end
end Dubon2026.SourceFunctionField.GammaOne
