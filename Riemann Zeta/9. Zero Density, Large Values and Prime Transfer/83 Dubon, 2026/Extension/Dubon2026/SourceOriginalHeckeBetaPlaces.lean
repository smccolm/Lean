import Dubon2026.SourceOriginalHeckeBetaGerms
import Dubon2026.SourceCurveCorrespondencePlaces
import Dubon2026.SourceOriginalHeckeFinite
import Dubon2026.SourceOriginalAnalyticPlaces

/-! DUB-17/18 -> original Picard-period Hecke comparison -> identification
of the actual analytic correspondence. Nonzero complex dilation preserves
meromorphic order. The proved beta germ identity therefore gives its exact
order formula and restriction on the genuine normalized analytic places.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem originalAnalyticOrder_heckeBeta (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    originalAnalyticOrder (N * ℓ) τ (originalHeckeBeta ℂ N ℓ x) =
      originalAnalyticOrder N (levelRaiseMatrix ℓ • τ) x := by
  unfold originalAnalyticOrder
  rw [meromorphicOrderAt_congr (original_realize_heckeBeta_eventuallyEq N ℓ x τ)]
  rw [coe_levelRaiseMatrix_smul]
  have hd : HasDerivAt (fun z : ℂ => (ℓ : ℂ) * z) (ℓ : ℂ) (τ : ℂ) := by
    simpa using (hasDerivAt_id (τ : ℂ)).const_mul (ℓ : ℂ)
  have ha : AnalyticAt ℂ (fun z : ℂ => (ℓ : ℂ) * z) (τ : ℂ) :=
    analyticAt_const.mul analyticAt_id
  exact meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) ha
    (by rw [hd.deriv]; exact Nat.cast_ne_zero.mpr (NeZero.ne ℓ))

theorem originalAnalyticPlace_restrict_heckeBeta (τ : ℍ) :
    Place.restrictAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
      (originalAnalyticPlace (N * ℓ) τ) = originalAnalyticPlace N (levelRaiseMatrix ℓ • τ) := by
  apply Place.ext
  ext x
  rw [Place.mem_restrictAlong_iff, originalAnalyticPlace_mem_iff,
    originalAnalyticPlace_mem_iff, originalAnalyticOrder_heckeBeta]

end
end Dubon2026.SourceFunctionField
