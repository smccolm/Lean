import Dubon2026.SourceEllipticOddTraceY

/-! The literal odd Velu coordinates are fixed by the actual cyclic translation
action. The subgroup's finiteness is derived from the actual point order, and
the normalized-sum identities are consumed explicitly. These are the invariant
coordinate inputs to the quotient equation, not a proof of that equation. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- Every actual kernel translation fixes the explicit odd quotient x-coordinate. -/
theorem translation_genericVeluX (hQ : addOrderOf Q = 2 * n + 1)
    (P : W.toAffine.Point) (hP : P ∈ AddSubgroup.zmultiples Q) :
    translation W.toAffine P (genericVeluX W (oddOrderSummingSet W Q n)) =
      genericVeluX W (oddOrderSummingSet W Q n) := by
  have hi := @translation_translationTraceX F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
    (finite_zmultiples_of_order hQ (by omega)) ⟨P, hP⟩
  have he := translationTraceX_eq_genericVeluX W hQ
  rw [he] at hi
  exact hi

/-- Every actual kernel translation fixes the explicit odd quotient y-coordinate. -/
theorem translation_genericVeluY (hQ : addOrderOf Q = 2 * n + 1)
    (P : W.toAffine.Point) (hP : P ∈ AddSubgroup.zmultiples Q) :
    translation W.toAffine P (genericVeluY W (oddOrderSummingSet W Q n)) =
      genericVeluY W (oddOrderSummingSet W Q n) := by
  have hi := @translation_translationTraceY F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
    (finite_zmultiples_of_order hQ (by omega)) ⟨P, hP⟩
  have he := translationTraceY_eq_genericVeluY W hQ
  rw [he] at hi
  exact hi

end Dubon2026.SourceEllipticFunctionField
