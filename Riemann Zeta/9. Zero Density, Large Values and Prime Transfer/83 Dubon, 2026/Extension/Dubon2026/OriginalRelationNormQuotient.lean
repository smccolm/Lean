import Dubon2026.OriginalNormQuotientCohomology
import Dubon2026.OriginalRelationNormExtension

/-! # The literal relation obstruction as a degree-two norm-quotient map

This identifies the precise injectivity problem still needed from the
normalized arithmetic class system. The constructed quotient and map are
actual coefficient objects; injectivity is not postulated. The existing
connecting isomorphism removes the H1-to-H2 change of presentation.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {G : Type} [Group G] [Fintype G] (B C : Rep.{0} ℤ G) [Finite B]

/-- The original connecting obstruction vanishes exactly when the actual degree-two norm-quotient image vanishes. This does not assert injectivity of that map. -/
theorem originalRelationObstruction_zero_iff_norm_quotient_image_zero
    (φ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C φ = 0 ↔
      originalNormQuotientCohomologyMap (originalRelationModule B) C 1
        (Submodule.Quotient.mk φ) = 0 := by
  rw [originalNormQuotientCohomologyMap_mk]
  exact originalRelationExtensionObstruction_zero_iff B C φ

end
end Dubon2026
