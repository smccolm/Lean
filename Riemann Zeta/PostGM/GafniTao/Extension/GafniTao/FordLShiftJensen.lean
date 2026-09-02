import GafniTao.FordLOffDiagonalAggregate
import Mathlib.Algebra.Order.Chebyshev

/-!
# Ford Lemma 3.3: sign symmetry and finite Jensen

The negative signed shifted sum is the conjugate of the positive one.  Thus
the one-coordinate parameter set has exactly `2 * (P / m)` equal-sign norm
terms.  Jensen's finite power inequality then produces the precise
`(2 * (P / m))^(k-1)` factor before the remaining one-coordinate sum.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

theorem fordLSignedShiftMoment_false_eq_neg_true
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (h : FordPositiveShift P m) (z : Fin P) :
    fordLSignedShiftMoment Ψ m (false, h) z =
      -fordLSignedShiftMoment Ψ m (true, h) z := by
  funext j
  simp [fordLSignedShiftMoment]

theorem fordLShiftedWeylSum_false_eq_conj_true
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (h : FordPositiveShift P m)
    (α : UnitAddTorus (Fin k)) :
    fordLShiftedWeylSum Ψ m (false, h) α =
      conj (fordLShiftedWeylSum Ψ m (true, h) α) := by
  unfold fordLShiftedWeylSum
  rw [ford_conj_characterSum]
  unfold fordCharacterSum
  apply Finset.sum_congr rfl
  intro z hz
  rw [fordLSignedShiftMoment_false_eq_neg_true]

theorem norm_fordLShiftedWeylSum_sign
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (η : Bool) (h : FordPositiveShift P m)
    (α : UnitAddTorus (Fin k)) :
    ‖fordLShiftedWeylSum Ψ m (η, h) α‖ =
      ‖fordLShiftedWeylSum Ψ m (true, h) α‖ := by
  cases η with
  | false => rw [fordLShiftedWeylSum_false_eq_conj_true, RCLike.norm_conj]
  | true => rfl

theorem fintype_card_bool_prod_fordPositiveShift (P m : ℕ) :
    Fintype.card (Bool × FordPositiveShift P m) = 2 * (P / m) := by
  rw [Fintype.card_prod]
  norm_num

theorem fordLShiftAmplitude_eq_two_mul_positive
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (α : UnitAddTorus (Fin k)) :
    fordLShiftAmplitude (P := P) Ψ m α =
      2 * ∑ h : FordPositiveShift P m,
        ‖fordLShiftedWeylSum Ψ m (true, h) α‖ := by
  unfold fordLShiftAmplitude
  rw [Fintype.sum_prod_type]
  simp_rw [norm_fordLShiftedWeylSum_sign]
  simp

theorem fordLShiftAmplitude_jensen
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (α : UnitAddTorus (Fin k)) (hk : 1 ≤ k) :
    fordLShiftAmplitude (P := P) Ψ m α ^ k ≤
      ((2 * (P / m) : ℕ) : ℝ) ^ (k - 1) *
        ∑ u : Bool × FordPositiveShift P m,
          ‖fordLShiftedWeylSum Ψ m u α‖ ^ k := by
  have h := pow_sum_le_card_mul_sum_pow
    (s := (Finset.univ : Finset (Bool × FordPositiveShift P m)))
    (f := fun u => ‖fordLShiftedWeylSum Ψ m u α‖)
    (fun _ _ => norm_nonneg _) (k - 1)
  rw [Nat.sub_add_cancel hk] at h
  simpa [fordLShiftAmplitude, fintype_card_bool_prod_fordPositiveShift] using h

theorem fordL_signed_power_sum_eq_two_mul_positive
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (m : ℕ) (α : UnitAddTorus (Fin k)) :
    (∑ u : Bool × FordPositiveShift P m,
        ‖fordLShiftedWeylSum Ψ m u α‖ ^ k) =
      2 * ∑ h : FordPositiveShift P m,
        ‖fordLShiftedWeylSum Ψ m (true, h) α‖ ^ k := by
  rw [Fintype.sum_prod_type]
  simp_rw [norm_fordLShiftedWeylSum_sign]
  simp

#print axioms fordLShiftedWeylSum_false_eq_conj_true
#print axioms fordLShiftAmplitude_jensen
#print axioms fordL_signed_power_sum_eq_two_mul_positive

end

end GafniTao
