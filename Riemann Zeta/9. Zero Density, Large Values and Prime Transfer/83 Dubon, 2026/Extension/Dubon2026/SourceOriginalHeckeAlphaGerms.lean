import Dubon2026.SourceOriginalFieldHomExt
import Dubon2026.SourceOriginalHeckeDegeneracy
import Dubon2026.SourceOriginalRealizationGermHom

/-! DUB-17/18 -> original Picard-period Hecke comparison -> actual analytic
degeneracy maps. The first degeneracy map is the inclusion of original
Laurent fields. The proved generator values identify its analytic realization
with the same upper-half-plane point, at every punctured germ.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem originalRealizeGerm_heckeAlpha (τ : ℍ) :
    (originalRealizeGerm (N * ℓ) τ).comp (originalHeckeAlpha ℂ N ℓ).toRingHom =
      originalRealizeGerm N τ := by
  apply original_field_ringHom_ext N
  · intro c
    change originalRealizeGerm (N * ℓ) τ
      (originalHeckeAlpha ℂ N ℓ (algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) = _
    rw [AlgHom.commutes, originalRealizeGerm_algebraMap, originalRealizeGerm_algebraMap]
  · apply Germ.coe_eq.mpr
    apply Eventually.of_forall
    intro z
    change realize (N * ℓ) (originalHeckeAlpha ℂ N ℓ (jOver N ℂ) : LaurentSeries ℂ)
      (ofComplex z) = realize N (jOver N ℂ : LaurentSeries ℂ) (ofComplex z)
    rw [originalHeckeAlpha_coe]
    exact (realize_coeffEmb_jq (N * ℓ) (ofComplex z)).trans (realize_jOver N (ofComplex z)).symm
  · apply Germ.coe_eq.mpr
    apply Eventually.of_forall
    intro z
    change realize (N * ℓ) (originalHeckeAlpha ℂ N ℓ (jNOver N ℂ) : LaurentSeries ℂ)
      (ofComplex z) = realize N (jNOver N ℂ : LaurentSeries ℂ) (ofComplex z)
    rw [originalHeckeAlpha_coe]
    exact (realize_coeffEmb_jqd (N * ℓ) N (dvd_mul_right N ℓ) (ofComplex z)).trans
      (realize_jNOver N (ofComplex z)).symm

theorem original_realize_heckeAlpha_eventuallyEq
    (x : modularFunctionFieldOver N ℂ) (τ : ℍ) :
    (fun z : ℂ => realize (N * ℓ) (originalHeckeAlpha ℂ N ℓ x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] fun z => realize N (x : LaurentSeries ℂ) (ofComplex z) :=
  Germ.coe_eq.mp (RingHom.congr_fun (originalRealizeGerm_heckeAlpha N ℓ τ) x)

end
end Dubon2026.SourceFunctionField
