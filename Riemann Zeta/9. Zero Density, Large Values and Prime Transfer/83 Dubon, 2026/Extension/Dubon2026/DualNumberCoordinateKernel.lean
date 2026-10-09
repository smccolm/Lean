import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.ToSquareZero

/-! # The actual dual-number kernel in coordinate lifting problems -/

namespace Dubon2026

noncomputable section

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Equality of original coordinate maps modulo the actual epsilon ideal is precisely equality of their ordinary coefficient reductions. -/
theorem dualNumberQuotient_comp_eq_iff (f g : A →ₐ[R] DualNumber R) :
    (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp f =
      (Ideal.Quotient.mkₐ R (TrivSqZeroExt.kerIdeal R R)).comp g ↔
        (TrivSqZeroExt.fstHom R R R).comp f = (TrivSqZeroExt.fstHom R R R).comp g := by
  rw [AlgHom.ext_iff, AlgHom.ext_iff]
  apply forall_congr'
  intro x
  change Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal R R) (f x) =
    Ideal.Quotient.mk (TrivSqZeroExt.kerIdeal R R) (g x) ↔ (f x).fst = (g x).fst
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom R R R) (f x - g x) = 0 ↔ _
  rw [map_sub, sub_eq_zero]
  rfl

/-- The actual epsilon kernel used by original first-order coordinate lifts has square zero. -/
theorem dualNumberCoordinateKernel_square_zero : (TrivSqZeroExt.kerIdeal R R) ^ 2 = ⊥ :=
  TrivSqZeroExt.kerIdeal_sq R R

end
end Dubon2026
