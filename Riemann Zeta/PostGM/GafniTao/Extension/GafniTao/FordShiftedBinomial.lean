import GafniTao.FordMomentTransform

/-!
# Ford equation (3.6): removal of the residue translation

For an interior shifted variable `u`, the physical integer is `p*u-a`.
The binomial transform which removes this translation therefore has parameter
`q*a`.  The following identities retain that scale exactly.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_shifted_base_add_translation
    {Q p : ℕ} [NeZero p] (q : ℕ) (c : ZMod p) (u : Fin (Q / p)) :
    (q : ℤ) *
          ((p * (u.1 + 1) - fordNegativeResidue p c : ℕ) : ℤ) +
        (q : ℤ) * (fordNegativeResidue p c : ℤ) =
      ((p * q : ℕ) : ℤ) * ((u.1 + 1 : ℕ) : ℤ) := by
  have ha : fordNegativeResidue p c ≤ p * (u.1 + 1) :=
    (fordNegativeResidue_lt c).le.trans
      (Nat.le_mul_of_pos_right p (by omega))
  rw [Nat.cast_sub ha]
  push_cast
  ring

theorem ford_shifted_scalar_binomial
    {Q p k : ℕ} [NeZero p] (q : ℕ) (c : ZMod p)
    (u : Fin (Q / p)) (j : Fin k) :
    ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
          ((u.1 + 1 : ℕ) : ℤ) ^ ((j : ℕ) + 1) =
      (q : ℤ) ^ ((j : ℕ) + 1) *
          ((p * (u.1 + 1) - fordNegativeResidue p c : ℕ) : ℤ) ^
            ((j : ℕ) + 1) +
        (∑ l : Fin (j : ℕ),
          (((j : ℕ) + 1).choose ((l : ℕ) + 1) : ℤ) *
            ((q : ℤ) * (fordNegativeResidue p c : ℤ)) ^
              ((j : ℕ) + 1 - ((l : ℕ) + 1)) *
            ((q : ℤ) ^ ((l : ℕ) + 1) *
              ((p * (u.1 + 1) - fordNegativeResidue p c : ℕ) : ℤ) ^
                ((l : ℕ) + 1))) +
        ((q : ℤ) * (fordNegativeResidue p c : ℤ)) ^
          ((j : ℕ) + 1) := by
  let X : ℤ := (q : ℤ) *
    ((p * (u.1 + 1) - fordNegativeResidue p c : ℕ) : ℤ)
  let A : ℤ := (q : ℤ) * (fordNegativeResidue p c : ℤ)
  have hXA : X + A =
      ((p * q : ℕ) : ℤ) * ((u.1 + 1 : ℕ) : ℤ) :=
    ford_shifted_base_add_translation q c u
  rw [← mul_pow, ← hXA, add_pow]
  rw [Finset.sum_range_succ']
  rw [show (j : ℕ) + 1 = (j : ℕ) + 1 by rfl]
  rw [Finset.sum_range_succ]
  simp only [Finset.sum_fin_eq_sum_range, Nat.choose_zero_right,
    pow_zero, one_mul, Nat.sub_zero,
    Nat.choose_self, Nat.sub_self]
  dsimp [X, A]
  simp only [mul_pow]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [if_pos (Finset.mem_range.mp hx)]

def fordS4InteriorPointMoment {k Q p : ℕ} [NeZero p]
    (q : ℕ) (c : ZMod p) (u : Fin (Q / p)) : Fin k → ℤ :=
  fun j ↦ (q : ℤ) ^ ((j : ℕ) + 1) *
    ((p * (u.1 + 1) - fordNegativeResidue p c : ℕ) : ℤ) ^
      ((j : ℕ) + 1)

theorem fordS4InteriorMoment_eq_sum_points
    {k s Q p : ℕ} [NeZero p] (q : ℕ) (c : ZMod p)
    (u : FordS4InteriorTuple s Q p) :
    fordS4InteriorMoment (k := k) q c u =
      ∑ i : Fin s, fordS4InteriorPointMoment (k := k) q c (u i) := by
  funext j
  simp [fordS4InteriorMoment, fordS4ShiftedMoment,
    fordS4InteriorTupleToShifted, fordInteriorToShiftIndex,
    fordS4InteriorPointMoment]

theorem fordS4InteriorPointMoment_transform
    {k Q p : ℕ} [NeZero p] (q : ℕ) (c : ZMod p)
    (u : Fin (Q / p)) (j : Fin k) :
    fordMomentBinomialTransform
          ((q : ℤ) * (fordNegativeResidue p c : ℤ))
          (fordS4InteriorPointMoment (k := k) q c u) j +
        ((q : ℤ) * (fordNegativeResidue p c : ℤ)) ^
          ((j : ℕ) + 1) =
      ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
        ((u.1 + 1 : ℕ) : ℤ) ^ ((j : ℕ) + 1) := by
  rw [ford_shifted_scalar_binomial q c u j]
  simp only [fordMomentBinomialTransform, fordMomentBinomialLower,
    fordS4InteriorPointMoment, Fin.val_castLE]

theorem fordS4InteriorMoment_transform
    {k s Q p : ℕ} [NeZero p] (q : ℕ) (c : ZMod p)
    (u : FordS4InteriorTuple s Q p) (j : Fin k) :
    fordMomentBinomialTransform
          ((q : ℤ) * (fordNegativeResidue p c : ℤ))
          (fordS4InteriorMoment (k := k) q c u) j +
        ∑ _i : Fin s,
          ((q : ℤ) * (fordNegativeResidue p c : ℤ)) ^
            ((j : ℕ) + 1) =
      ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerSumInt u ((j : ℕ) + 1) := by
  rw [fordS4InteriorMoment_eq_sum_points]
  rw [show fordMomentBinomialTransform
        ((q : ℤ) * (fordNegativeResidue p c : ℤ))
        (∑ i : Fin s, fordS4InteriorPointMoment (k := k) q c (u i)) =
      ∑ i : Fin s,
        fordMomentBinomialTransform
          ((q : ℤ) * (fordNegativeResidue p c : ℤ))
          (fordS4InteriorPointMoment (k := k) q c (u i)) by
    simpa only [fordMomentBinomialTransformHom_apply] using
      map_sum (fordMomentBinomialTransformHom
        ((q : ℤ) * (fordNegativeResidue p c : ℤ)))
        (fun i : Fin s ↦ fordS4InteriorPointMoment (k := k) q c (u i))
        Finset.univ]
  simp only [Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  unfold fordPowerSumInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact fordS4InteriorPointMoment_transform q c (u i) j

#print axioms ford_shifted_base_add_translation
#print axioms ford_shifted_scalar_binomial
#print axioms fordS4InteriorMoment_transform

end

end GafniTao
