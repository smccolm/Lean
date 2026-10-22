import Dubon2026.SourceOriginalFieldHomExt
import Dubon2026.SourceOriginalHeckeDegeneracy
import Dubon2026.SourceGermPullback
import Dubon2026.SourceOriginalRealizationGermHom
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual analytic
degeneracy maps. The second degeneracy map substitutes q to q raised to ell.
The two original generators identify its analytic germ with dilation by ell.
All equalities concern the actual original field and its realized functions.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [NeZero N] in
theorem originalHeckeBeta_jOver_coe :
    (originalHeckeBeta ℂ N ℓ (jOver N ℂ) : LaurentSeries ℂ) =
      coeffEmb ℂ (qExpand ℚ ℓ jq) := by
  rw [originalHeckeBeta_coe]
  exact (coeffMap_qExpand (algebraMap ℚ ℂ) ℓ jq).symm

theorem originalHeckeBeta_jNOver_coe :
    (originalHeckeBeta ℂ N ℓ (jNOver N ℂ) : LaurentSeries ℂ) =
      coeffEmb ℂ (qExpand ℚ (N * ℓ) jq) := by
  rw [originalHeckeBeta_coe]
  change qExpand ℂ ℓ (coeffEmb ℂ (qExpand ℚ N jq)) = _
  calc
    _ = coeffEmb ℂ (qExpand ℚ ℓ (qExpand ℚ N jq)) :=
      (coeffMap_qExpand (algebraMap ℚ ℂ) ℓ (qExpand ℚ N jq)).symm
    _ = _ := by simp only [qExpand_qExpand, mul_comm ℓ N]

omit [NeZero N] in
theorem tendsto_dilation_nhdsNE (τ : ℍ) :
    Tendsto (fun z : ℂ => (ℓ : ℂ) * z) (𝓝[≠] (τ : ℂ))
      (𝓝[≠] ((levelRaiseMatrix ℓ • τ : ℍ) : ℂ)) := by
  have h : HasDerivAt (fun z : ℂ => (ℓ : ℂ) * z) (ℓ : ℂ) (τ : ℂ) := by
    simpa using (hasDerivAt_id (τ : ℂ)).const_mul (ℓ : ℂ)
  rw [coe_levelRaiseMatrix_smul]
  exact h.tendsto_nhdsNE (Nat.cast_ne_zero.mpr (NeZero.ne ℓ))

omit [NeZero N] in
theorem ofComplex_dilation {z : ℂ} (hz : 0 < z.im) :
    ofComplex ((ℓ : ℂ) * z) = levelRaiseMatrix ℓ • ofComplex z := by
  rw [ofComplex_apply_of_im_pos hz]
  have he := coe_levelRaiseMatrix_smul ℓ (⟨z, hz⟩ : ℍ)
  change ((levelRaiseMatrix ℓ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) = (ℓ : ℂ) * z at he
  rw [← he, ofComplex_apply]

theorem originalRealizeGerm_heckeBeta (τ : ℍ) :
    (originalRealizeGerm (N * ℓ) τ).comp (originalHeckeBeta ℂ N ℓ).toRingHom =
      (germPullback (fun z : ℂ => (ℓ : ℂ) * z) (tendsto_dilation_nhdsNE ℓ τ)).comp
        (originalRealizeGerm N (levelRaiseMatrix ℓ • τ)) := by
  apply original_field_ringHom_ext N
  · intro c
    change originalRealizeGerm (N * ℓ) τ
      (originalHeckeBeta ℂ N ℓ (algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) = _
    rw [AlgHom.commutes, originalRealizeGerm_algebraMap,
      RingHom.comp_apply, originalRealizeGerm_algebraMap, germPullback_coe]
    rfl
  · apply Germ.coe_eq.mpr
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz
    change realize (N * ℓ) (originalHeckeBeta ℂ N ℓ (jOver N ℂ) : LaurentSeries ℂ)
      (ofComplex z) = realize N (jOver N ℂ : LaurentSeries ℂ) (ofComplex ((ℓ : ℂ) * z))
    rw [originalHeckeBeta_jOver_coe, realize_coeffEmb_jqd (N * ℓ) ℓ (dvd_mul_left ℓ N),
      realize_jOver, ofComplex_dilation ℓ hz]
  · apply Germ.coe_eq.mpr
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz
    change realize (N * ℓ) (originalHeckeBeta ℂ N ℓ (jNOver N ℂ) : LaurentSeries ℂ)
      (ofComplex z) = realize N (jNOver N ℂ : LaurentSeries ℂ) (ofComplex ((ℓ : ℂ) * z))
    rw [originalHeckeBeta_jNOver_coe, realize_coeffEmb_jqd (N * ℓ) (N * ℓ) dvd_rfl,
      realize_jNOver, ofComplex_dilation ℓ hz]
    have he : levelRaiseMatrix (N * ℓ) • ofComplex z =
        levelRaiseMatrix N • (levelRaiseMatrix ℓ • ofComplex z) := by
      apply UpperHalfPlane.ext
      simp only [coe_levelRaiseMatrix_smul, Nat.cast_mul, mul_assoc]
    rw [he]

theorem original_realize_heckeBeta_eventuallyEq
    (x : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => realize (N * ℓ) (originalHeckeBeta ℂ N ℓ x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun z => realize N (x : LaurentSeries ℂ) (ofComplex ((ℓ : ℂ) * z)) :=
  Germ.coe_eq.mp (RingHom.congr_fun (originalRealizeGerm_heckeBeta N ℓ τ) x)

end
end Dubon2026.SourceFunctionField
