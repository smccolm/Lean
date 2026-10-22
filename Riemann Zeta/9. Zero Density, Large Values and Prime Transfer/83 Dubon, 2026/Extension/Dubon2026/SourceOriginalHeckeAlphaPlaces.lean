import Dubon2026.SourceOriginalHeckeAlphaGerms
import Dubon2026.SourceCurveCorrespondencePlaces
import Dubon2026.SourceOriginalHeckeFinite
import Dubon2026.SourceOriginalAnalyticPlaces

/-! DUB-17/18 -> original Picard-period Hecke comparison -> identification
of the actual analytic correspondence. The inclusion degeneracy map fixes
the upper-half-plane point. Its germ identity proves the exact analytic
order equality and hence the restriction identity for actual places.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

theorem originalAnalyticOrder_heckeAlpha (τ : ℍ) (x : modularFunctionFieldOver N ℂ) :
    originalAnalyticOrder (N * ℓ) τ (originalHeckeAlpha ℂ N ℓ x) =
      originalAnalyticOrder N τ x :=
  meromorphicOrderAt_congr (original_realize_heckeAlpha_eventuallyEq N ℓ x τ)

theorem originalAnalyticPlace_restrict_heckeAlpha (τ : ℍ) :
    Place.restrictAlong (originalHeckeAlpha ℂ N ℓ) (originalHeckeAlpha_finite ℂ N ℓ)
      (originalAnalyticPlace (N * ℓ) τ) = originalAnalyticPlace N τ := by
  apply Place.ext
  ext x
  rw [Place.mem_restrictAlong_iff, originalAnalyticPlace_mem_iff,
    originalAnalyticPlace_mem_iff, originalAnalyticOrder_heckeAlpha]

end
end Dubon2026.SourceFunctionField
