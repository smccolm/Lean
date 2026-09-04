import GafniTao.HeathBrownCoefficientPhase
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Variation of the literal coefficient-change weight

Membership in the Heath-Brown cell gives `|β_j| ≤ H^(-j)`.  On every
source edge `q → q+1`, the associated polynomial phase changes by at most
`k²/H`; hence the exact exponential weight changes by at most
`2π k²/H`.  These are the quantitative inputs to the second Abel summation.
-/

open Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem abs_natCast_succ_pow_sub_pow_le
    {q d H : ℕ} (hqH : q + 1 ≤ H) :
    |((q : ℝ) + 1) ^ d - (q : ℝ) ^ d| ≤
      (d : ℝ) * (H : ℝ) ^ (d - 1) := by
  have hq : (0 : ℝ) ≤ q := by positivity
  have hqsucc : (0 : ℝ) ≤ q + 1 := by positivity
  have hqh : (q : ℝ) + 1 ≤ H := by exact_mod_cast hqH
  calc
    |((q : ℝ) + 1) ^ d - (q : ℝ) ^ d| ≤
        |((q : ℝ) + 1 - (q : ℝ))| * d *
          max |((q : ℝ) + 1)| |(q : ℝ)| ^ (d - 1) :=
      abs_pow_sub_pow_le ((q : ℝ) + 1) (q : ℝ) d
    _ = (d : ℝ) * (((q : ℝ) + 1) ^ (d - 1)) := by
      have hqle : (q : ℝ) ≤ (q : ℝ) + 1 := by linarith
      rw [abs_of_nonneg hqsucc, abs_of_nonneg hq, max_eq_left hqle]
      norm_num
    _ ≤ (d : ℝ) * (H : ℝ) ^ (d - 1) := by
      gcongr

theorem cell_displacement_mul_powerDifference_le
    {k H : ℕ} (hH : 2 ≤ H) {f : ℝ → ℝ} {n : ℝ}
    {α : HeathBrownCoefficientTorus k}
    (hα : α ∈ heathBrownCoefficientCell k H f n)
    {q : ℕ} (hqH : q + 1 ≤ H) (j : Fin (k - 1)) :
    |heathBrownCoefficientDisplacement
        (heathBrownCoefficientCenter k f n) α j| *
        |((q : ℝ) + 1) ^ ((j : ℕ) + 1) -
          (q : ℝ) ^ ((j : ℕ) + 1)| ≤
      (k : ℝ) / H := by
  let d : ℕ := (j : ℕ) + 1
  have hd : 1 ≤ d := by simp [d]
  have hdk : d ≤ k := by
    dsimp [d]
    have hj := j.isLt
    omega
  have hHpos : (0 : ℝ) < H := by positivity
  have hβ := abs_heathBrownCoefficientDisplacement_le_radius hα j
  have hpow := abs_natCast_succ_pow_sub_pow_le (d := d) hqH
  have hpowNonneg : (0 : ℝ) ≤ (d : ℝ) * (H : ℝ) ^ (d - 1) := by positivity
  calc
    |heathBrownCoefficientDisplacement
        (heathBrownCoefficientCenter k f n) α j| *
        |((q : ℝ) + 1) ^ d - (q : ℝ) ^ d| ≤
      heathBrownCellRadius H j *
        ((d : ℝ) * (H : ℝ) ^ (d - 1)) :=
      mul_le_mul hβ hpow (abs_nonneg _) (by
        exact (heathBrownCellRadius_pos (by omega : 1 ≤ H) j).le)
    _ = (d : ℝ) / H := by
      unfold heathBrownCellRadius
      dsimp [d]
      rw [pow_succ]
      field_simp
    _ ≤ (k : ℝ) / H := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hdk) hHpos.le

theorem abs_heathBrownDisplacementPolynomial_succ_sub_le
    {k H : ℕ} (hH : 2 ≤ H) {f : ℝ → ℝ} {n : ℝ}
    {α : HeathBrownCoefficientTorus k}
    (hα : α ∈ heathBrownCoefficientCell k H f n)
    {q : ℕ} (hqH : q + 1 ≤ H) :
    |heathBrownDisplacementPolynomial
          (heathBrownCoefficientCenter k f n) α (q + 1) -
        heathBrownDisplacementPolynomial
          (heathBrownCoefficientCenter k f n) α q| ≤
      (k : ℝ) ^ 2 / H := by
  unfold heathBrownDisplacementPolynomial
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin (k - 1),
        (heathBrownCoefficientDisplacement
            (heathBrownCoefficientCenter k f n) α j *
              ((q : ℝ) + 1) ^ ((j : ℕ) + 1) -
          heathBrownCoefficientDisplacement
            (heathBrownCoefficientCenter k f n) α j *
              (q : ℝ) ^ ((j : ℕ) + 1))| ≤
        ∑ j : Fin (k - 1),
          |heathBrownCoefficientDisplacement
              (heathBrownCoefficientCenter k f n) α j| *
            |((q : ℝ) + 1) ^ ((j : ℕ) + 1) -
              (q : ℝ) ^ ((j : ℕ) + 1)| := by
      calc
        |∑ j : Fin (k - 1),
            (heathBrownCoefficientDisplacement
                (heathBrownCoefficientCenter k f n) α j *
                  ((q : ℝ) + 1) ^ ((j : ℕ) + 1) -
              heathBrownCoefficientDisplacement
                (heathBrownCoefficientCenter k f n) α j *
                  (q : ℝ) ^ ((j : ℕ) + 1))| ≤
            ∑ j : Fin (k - 1),
              |heathBrownCoefficientDisplacement
                  (heathBrownCoefficientCenter k f n) α j *
                    ((q : ℝ) + 1) ^ ((j : ℕ) + 1) -
                heathBrownCoefficientDisplacement
                  (heathBrownCoefficientCenter k f n) α j *
                    (q : ℝ) ^ ((j : ℕ) + 1)| := abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [← mul_sub, abs_mul]
    _ ≤ ∑ _j : Fin (k - 1), (k : ℝ) / H := by
      exact Finset.sum_le_sum fun j hj =>
        cell_displacement_mul_powerDifference_le hH hα hqH j
    _ ≤ (k : ℝ) ^ 2 / H := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      have hcard : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      have hdiv : 0 ≤ (k : ℝ) / H := by positivity
      calc
        ((k - 1 : ℕ) : ℝ) * ((k : ℝ) / H) ≤
            (k : ℝ) * ((k : ℝ) / H) :=
          mul_le_mul_of_nonneg_right hcard hdiv
        _ = (k : ℝ) ^ 2 / H := by ring

theorem norm_heathBrownCoefficientWeight_succ_sub_le
    {k H : ℕ} (hH : 2 ≤ H) {f : ℝ → ℝ} {n : ℝ}
    {α : HeathBrownCoefficientTorus k}
    (hα : α ∈ heathBrownCoefficientCell k H f n)
    {q : ℕ} (hqH : q + 1 ≤ H) :
    ‖heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α (q + 1) -
        heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α q‖ ≤
      2 * Real.pi * ((k : ℝ) ^ 2 / H) := by
  unfold heathBrownCoefficientWeight
  simp only [Nat.cast_add, Nat.cast_one]
  have hphase := norm_heathBrownPhase_sub_le
    (-heathBrownDisplacementPolynomial
      (heathBrownCoefficientCenter k f n) α (q + 1))
    (-heathBrownDisplacementPolynomial
      (heathBrownCoefficientCenter k f n) α q)
  calc
    ‖heathBrownPhase
          (-heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α (q + 1)) -
        heathBrownPhase
          (-heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α q)‖ ≤
      2 * Real.pi *
        |(-heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α (q + 1)) -
          (-heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α q)| := hphase
    _ = 2 * Real.pi *
        |heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α (q + 1) -
          heathBrownDisplacementPolynomial
            (heathBrownCoefficientCenter k f n) α q| := by
      rw [← abs_neg]
      congr 2
      ring
    _ ≤ 2 * Real.pi * ((k : ℝ) ^ 2 / H) := by
      gcongr
      exact abs_heathBrownDisplacementPolynomial_succ_sub_le hH hα hqH

#print axioms abs_natCast_succ_pow_sub_pow_le
#print axioms cell_displacement_mul_powerDifference_le
#print axioms abs_heathBrownDisplacementPolynomial_succ_sub_le
#print axioms norm_heathBrownCoefficientWeight_succ_sub_le

end

end GafniTao
