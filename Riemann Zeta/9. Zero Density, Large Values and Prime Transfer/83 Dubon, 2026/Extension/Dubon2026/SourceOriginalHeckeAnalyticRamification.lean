import Dubon2026.SourceOriginalHeckeAlphaPlaces
import Dubon2026.SourceOriginalHeckeBetaPlaces

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the exact
divisor correspondence on analytic points. The actual germ orders identify
the integer ramification weights of both finite maps, including elliptic
points. These weights are required for the later double-coset divisor sum.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem originalHeckeAlpha_analytic_ramification (τ : ℍ) :
    (originalAnalyticRamification N τ : ℤ) =
      (originalAnalyticRamification (N * ℓ) τ : ℤ) *
        Place.ramificationAlong (originalHeckeAlpha ℂ N ℓ) (originalHeckeAlpha_finite ℂ N ℓ)
          (originalAnalyticPlace (N * ℓ) τ) := by
  let v := originalAnalyticPlace N τ
  have h := originalAnalyticPlace_order (N * ℓ) τ (originalHeckeAlpha ℂ N ℓ v.uniformizer)
    ((map_ne_zero _).mpr v.uniformizer_ne_zero)
  rw [originalAnalyticOrder_heckeAlpha,
    originalAnalyticPlace_order N τ v.uniformizer v.uniformizer_ne_zero,
    Place.ord_uniformizer, mul_one] at h
  rw [Place.ramificationAlong, originalAnalyticPlace_restrict_heckeAlpha]
  exact WithTop.coe_injective h

theorem originalHeckeBeta_analytic_ramification (τ : ℍ) :
    (originalAnalyticRamification N (levelRaiseMatrix ℓ • τ) : ℤ) =
      (originalAnalyticRamification (N * ℓ) τ : ℤ) *
        Place.ramificationAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
          (originalAnalyticPlace (N * ℓ) τ) := by
  let v := originalAnalyticPlace N (levelRaiseMatrix ℓ • τ)
  have h := originalAnalyticPlace_order (N * ℓ) τ (originalHeckeBeta ℂ N ℓ v.uniformizer)
    ((map_ne_zero _).mpr v.uniformizer_ne_zero)
  rw [originalAnalyticOrder_heckeBeta,
    originalAnalyticPlace_order N (levelRaiseMatrix ℓ • τ) v.uniformizer v.uniformizer_ne_zero,
    Place.ord_uniformizer, mul_one] at h
  rw [Place.ramificationAlong, originalAnalyticPlace_restrict_heckeBeta]
  exact WithTop.coe_injective h

end
end Dubon2026.SourceFunctionField
