import Dubon2026.SourceEllipticTranslationFixedField
import Dubon2026.SourceEllipticOddTranslationInvariance
import Dubon2026.SourceEllipticOddFieldTower

/-! The actual odd cyclic fixed field has index 2n+1 and is quadratic over the
explicit Velu x-coordinate field. The actual x- and y-formulas lie in it.
These derive the finite separable quotient-field prerequisite without assuming
the explicit quotient equation, which remains to be proved on DUB-17/18. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open scoped IntermediateField

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- The literal odd x-coordinate belongs to the actual cyclic translation fixed field. -/
theorem genericVeluX_mem_oddFixedField (hQ : addOrderOf Q = 2 * n + 1) :
    genericVeluX W (oddOrderSummingSet W Q n) ∈
      translationFixedField W.toAffine (AddSubgroup.zmultiples Q) := by
  rw [mem_translationFixedField_iff]
  exact translation_genericVeluX W hQ

/-- The literal odd y-coordinate belongs to the actual cyclic translation fixed field. -/
theorem genericVeluY_mem_oddFixedField (hQ : addOrderOf Q = 2 * n + 1) :
    genericVeluY W (oddOrderSummingSet W Q n) ∈
      translationFixedField W.toAffine (AddSubgroup.zmultiples Q) := by
  rw [mem_translationFixedField_iff]
  exact translation_genericVeluY W hQ

/-- The actual odd fixed-field index equals the generator's order. -/
theorem finrank_oddFixedField (hQ : addOrderOf Q = 2 * n + 1) :
    Module.finrank (translationFixedField W.toAffine (AddSubgroup.zmultiples Q))
      W.toAffine.FunctionField = 2 * n + 1 := by
  have h := @finrank_translationFixedField F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
    (finite_zmultiples_of_order hQ (by omega))
  exact h.trans ((Nat.card_zmultiples Q).trans hQ)

/-- The actual odd fixed-field extension is Galois, including in its residue characteristic. -/
theorem isGalois_oddFixedField (hQ : addOrderOf Q = 2 * n + 1) :
    IsGalois (translationFixedField W.toAffine (AddSubgroup.zmultiples Q))
      W.toAffine.FunctionField :=
  @isGalois_translationFixedField F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
    (finite_zmultiples_of_order hQ (by omega))

/-- The actual cyclic fixed field is quadratic over the literal odd quotient x-coordinate. -/
theorem relfinrank_odd_coordinate_fixedField (hQ : addOrderOf Q = 2 * n + 1) :
    IntermediateField.relfinrank F⟮genericVeluX W (oddOrderSummingSet W Q n)⟯
      (translationFixedField W.toAffine (AddSubgroup.zmultiples Q)) = 2 := by
  have hle := IntermediateField.adjoin_simple_le_iff.mpr (genericVeluX_mem_oddFixedField W hQ)
  have h := IntermediateField.relfinrank_mul_finrank_top hle
  rw [finrank_oddFixedField W hQ, finrank_odd_generic_coordinate hQ] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * n + 1) h

end Dubon2026.SourceEllipticFunctionField
