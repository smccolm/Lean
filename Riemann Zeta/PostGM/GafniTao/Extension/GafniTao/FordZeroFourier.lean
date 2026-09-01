import GafniTao.FordIntegerDifferenceSystem

/-!
# Finite zero-frequency orthogonality

This is the one-family counterpart of the collision identity used elsewhere
in Ford's argument.  It counts the exact zero fibres of an arbitrary finite
integer-vector moment family.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def FordCharacterZero {k : ℕ} {A : Type*}
    (M : A → Fin k → ℤ) := {a : A // M a = 0}

instance fordCharacterZeroFinite
    {k : ℕ} {A : Type*} [Fintype A] (M : A → Fin k → ℤ) :
    Finite (FordCharacterZero M) :=
  Finite.of_injective Subtype.val Subtype.val_injective

theorem ford_character_sum_mean_eq_zero_count
    {k : ℕ} {A : Type*} [Fintype A]
    (M : A → Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k), fordCharacterSum M α
        ∂fordTorusMeasure k =
      (Nat.card (FordCharacterZero M) : ℂ) := by
  letI : Fintype (FordCharacterZero M) := Fintype.ofFinite _
  unfold fordCharacterSum
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun a _ => ford_integrable_mFourier_pi_haar (M a))]
  simp_rw [ford_integral_mFourier_pi_haar_eq]
  rw [Nat.card_eq_fintype_card]
  unfold FordCharacterZero
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

#print axioms ford_character_sum_mean_eq_zero_count

end

end GafniTao
