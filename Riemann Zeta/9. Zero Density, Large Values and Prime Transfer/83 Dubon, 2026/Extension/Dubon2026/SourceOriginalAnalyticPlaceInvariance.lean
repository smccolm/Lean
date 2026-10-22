import Dubon2026.SourceOriginalAnalyticPlaceBoundedness

/-! DUB-17/18 -> original analytic-place dictionary -> modular
regular-differential realization. Equal weights cancel in the actual
modular quotient, making its germ invariant under Gamma0(N). Native
invariance of meromorphic order under the Mobius coordinate change then
identifies the genuine normalized places on each modular orbit.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_complexPlaceDictionary.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology

theorem original_realize_smul_eventuallyEq (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    (fun z : ℂ => realize N (x : LaurentSeries ℂ)
      (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) • ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨k, g, h, hh, hx⟩ := original_field_modular_ratio N x
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
  rw [hsm, realize_eq_div N g h x hx _ hne, realize_eq_div N g h x hx _ hz,
    hgγ, hhγ, mul_div_mul_left _ _ hd]

theorem originalAnalyticOrder_smul (N : ℕ) [NeZero N]
    (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    originalAnalyticOrder N ((γ : SL(2, ℤ)) • τ) x = originalAnalyticOrder N τ x := by
  unfold originalAnalyticOrder
  have hdet1 : (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hdet : 0 < (((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)).val.det := by rw [hdet1]; exact one_pos
  rw [show ((((γ : SL(2, ℤ)) • τ : ℍ)) : ℂ) = ↑((((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)) • τ) by simp,
    ← meromorphicOrderAt_comp_smul hdet]
  exact meromorphicOrderAt_congr (original_realize_smul_eventuallyEq N x γ τ)

theorem originalAnalyticPlace_smul (N : ℕ) [NeZero N]
    (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    originalAnalyticPlace N ((γ : SL(2, ℤ)) • τ) = originalAnalyticPlace N τ := by
  apply SourceCurve.Place.ext
  apply SetLike.ext
  intro x
  rw [originalAnalyticPlace_mem_iff, originalAnalyticPlace_mem_iff, originalAnalyticOrder_smul]

end
end Dubon2026.SourceFunctionField
