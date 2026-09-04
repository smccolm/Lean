import GafniTao.HeathBrownCoefficientCells
import Mathlib.Data.ENNReal.BigOperators

/-!
# The exact volume factor in Heath-Brown's coefficient cells

This file evaluates the product of the `k - 1` coordinate radii.  It is the
literal factor `2^(k-1) H^(-k(k-1)/2)` occurring immediately after the
definition of `nu(alpha)` in the proof of Lemma 1.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem sum_range_succ_eq_heathBrownCriticalMoment (k : ℕ) :
    (∑ j ∈ Finset.range (k - 1), (j + 1)) = heathBrownCriticalMoment k := by
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_range_id]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  unfold heathBrownCriticalMoment
  rw [← Nat.choose_two_right (k - 1), ← Nat.choose_two_right k]
  cases k with
  | zero => simp
  | succ k => simp [Nat.choose, Nat.add_comm]

theorem sum_fin_succ_eq_heathBrownCriticalMoment (k : ℕ) :
    (∑ j : Fin (k - 1), ((j : ℕ) + 1)) = heathBrownCriticalMoment k := by
  calc
    _ = ∑ j ∈ Finset.range (k - 1), (j + 1) :=
      by simpa only using
        (Fin.sum_univ_eq_sum_range (fun j : ℕ => j + 1) (k - 1))
    _ = _ := sum_range_succ_eq_heathBrownCriticalMoment k

theorem prod_heathBrownCellRadius
    {k H : ℕ} :
    (∏ j : Fin (k - 1), heathBrownCellRadius H j) =
      (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹) := by
  simp only [heathBrownCellRadius]
  rw [Finset.prod_inv_distrib]
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (H : ℝ) ^ (j + 1)) (k - 1)]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 2
  exact sum_range_succ_eq_heathBrownCriticalMoment k

theorem prod_two_mul_heathBrownCellRadius
    {k H : ℕ} :
    (∏ j : Fin (k - 1), (2 * heathBrownCellRadius H j)) =
      (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [prod_heathBrownCellRadius]

theorem measure_heathBrownCoefficientCell_exact
    {k H : ℕ} (hH : 2 ≤ H) (f : ℝ → ℝ) (n : ℝ) :
    Measure.pi (fun _ : Fin (k - 1) => AddCircle.haarAddCircle)
        (heathBrownCoefficientCell k H f n) =
      ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) := by
  rw [measure_heathBrownCoefficientCell hH]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · rw [prod_two_mul_heathBrownCellRadius]
  · intro j hj
    exact mul_nonneg (by norm_num)
      (le_of_lt (heathBrownCellRadius_pos (by omega) j))

theorem measureReal_heathBrownCoefficientCell_exact
    {k H : ℕ} (hH : 2 ≤ H) (f : ℝ → ℝ) (n : ℝ) :
    (Measure.pi (fun _ : Fin (k - 1) => AddCircle.haarAddCircle)).real
        (heathBrownCoefficientCell k H f n) =
      (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹) := by
  unfold Measure.real
  rw [measure_heathBrownCoefficientCell_exact hH f n]
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity) (by positivity)

#print axioms sum_range_succ_eq_heathBrownCriticalMoment
#print axioms sum_fin_succ_eq_heathBrownCriticalMoment
#print axioms prod_heathBrownCellRadius
#print axioms prod_two_mul_heathBrownCellRadius
#print axioms measure_heathBrownCoefficientCell_exact
#print axioms measureReal_heathBrownCoefficientCell_exact

end

end GafniTao
