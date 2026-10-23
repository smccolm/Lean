import Dubon2026.SourceEllipticOddQuotientPullback
import Dubon2026.SourceEllipticCoordinateImageDegree

/-! The actual odd quotient pullback has the prescribed degree and its image
is exactly the cyclic translation fixed field. Thus this actual extension is
Galois and separable, even in residue characteristic. This discharges the
field-extension hypotheses preceding the integral closure and point-map
construction on the DUB-17/18 odd quotient dependency. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped IntermediateField

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual quotient image is quadratic over the literal quotient x-coordinate. -/
theorem relfinrank_oddQuotient_coordinate (hQ : addOrderOf Q = 2 * n + 1) :
    IntermediateField.relfinrank F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯
      (oddQuotientPullback W hQ).fieldRange = 2 := by
  simpa only [oddQuotientPullback_genericX] using
    relfinrank_coordinate_image (veluQuotient W (oddOrderSummingSet W Q n)) (oddQuotientPullback W hQ)

/-- The actual odd quotient embedding has degree exactly the order of its cyclic subgroup. -/
theorem finrank_oddQuotient_range (hQ : addOrderOf Q = 2 * n + 1) :
    Module.finrank (oddQuotientPullback W hQ).fieldRange W.toAffine.FunctionField = 2 * n + 1 := by
  have hle : F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯ ≤ (oddQuotientPullback W hQ).fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr ⟨_, oddQuotientPullback_genericX W hQ⟩
  have h := IntermediateField.relfinrank_mul_finrank_top hle
  rw [relfinrank_oddQuotient_coordinate W hQ, finrank_odd_generic_coordinate hQ] at h
  omega

/-- The literal odd quotient image equals the actual cyclic translation fixed field. -/
theorem oddQuotientPullback_range_eq_fixedField (hQ : addOrderOf Q = 2 * n + 1) :
    (oddQuotientPullback W hQ).fieldRange = translationFixedField W.toAffine (AddSubgroup.zmultiples Q) := by
  have hle := oddQuotientPullback_range_le_fixedField W hQ
  have h := IntermediateField.relfinrank_mul_finrank_top hle
  rw [finrank_oddFixedField W hQ, finrank_oddQuotient_range W hQ] at h
  have hrel : IntermediateField.relfinrank (oddQuotientPullback W hQ).fieldRange
      (translationFixedField W.toAffine (AddSubgroup.zmultiples Q)) = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n + 1)
    simpa only [one_mul] using h
  exact le_antisymm hle (IntermediateField.relfinrank_eq_one_iff.mp hrel)

/-- Finite dimensionality of the actual odd quotient extension is proved from its exact degree. -/
theorem finiteDimensional_oddQuotient_range (hQ : addOrderOf Q = 2 * n + 1) :
    FiniteDimensional (oddQuotientPullback W hQ).fieldRange W.toAffine.FunctionField :=
  .of_finrank_pos (by rw [finrank_oddQuotient_range W hQ]; omega)

/-- The actual odd quotient extension is Galois through the proved fixed-field identification. -/
theorem isGalois_oddQuotient_range (hQ : addOrderOf Q = 2 * n + 1) :
    IsGalois (oddQuotientPullback W hQ).fieldRange W.toAffine.FunctionField := by
  rw [oddQuotientPullback_range_eq_fixedField W hQ]
  exact isGalois_oddFixedField W hQ

/-- Separability of the actual odd quotient extension requires no characteristic exclusion. -/
theorem isSeparable_oddQuotient_range (hQ : addOrderOf Q = 2 * n + 1) :
    Algebra.IsSeparable (oddQuotientPullback W hQ).fieldRange W.toAffine.FunctionField := by
  letI := isGalois_oddQuotient_range W hQ
  infer_instance

end Dubon2026.SourceEllipticFunctionField
