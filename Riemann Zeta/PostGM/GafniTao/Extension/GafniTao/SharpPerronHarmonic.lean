import GafniTao.SharpPerronLSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The half-integral harmonic kernel

Evaluating Perron's formula at a half-integer removes the endpoint
singularity.  The remaining near-diagonal reciprocal distances form two
copies of a harmonic sum.  The estimates here keep that combinatorics exact.
-/

open scoped BigOperators

namespace GafniTao

private theorem sum_two_div_nat_succ_eq_two_mul_harmonic (m : ℕ) :
    (∑ k ∈ Finset.range m, 2 / ((k + 1 : ℕ) : ℝ)) =
      2 * (harmonic m : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  field_simp

private theorem left_half_distance_sum_le (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1),
      1 / |(m : ℝ) + 1 / 2 - (n : ℝ)|) ≤
        2 * (harmonic (m + 1) : ℝ) := by
  calc
    (∑ n ∈ Finset.range (m + 1),
        1 / |(m : ℝ) + 1 / 2 - (n : ℝ)|) ≤
      ∑ n ∈ Finset.range (m + 1),
        2 / (((m - n) + 1 : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnm : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
          have hdist :
              |(m : ℝ) + 1 / 2 - (n : ℝ)| =
                (m - n : ℕ) + 1 / 2 := by
            rw [abs_of_nonneg]
            · rw [Nat.cast_sub hnm]
              ring
            · exact sub_nonneg.mpr (by
                have : (n : ℝ) ≤ m := by exact_mod_cast hnm
                linarith)
          rw [hdist]
          have hden : 0 < ((m - n : ℕ) : ℝ) + 1 / 2 := by positivity
          have hnat : 0 < (((m - n) + 1 : ℕ) : ℝ) := by positivity
          rw [div_le_div_iff₀ hden hnat]
          push_cast
          nlinarith
    _ = ∑ k ∈ Finset.range (m + 1), 2 / ((k + 1 : ℕ) : ℝ) := by
      rw [← Finset.sum_range_reflect
        (fun k => 2 / ((k + 1 : ℕ) : ℝ)) (m + 1)]
      apply Finset.sum_congr rfl
      intro n hn
      congr 2
    _ = 2 * (harmonic (m + 1) : ℝ) :=
      sum_two_div_nat_succ_eq_two_mul_harmonic (m + 1)

private theorem right_half_distance_sum_le (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1),
      1 / |(m : ℝ) + 1 / 2 - ((m + 1 + k : ℕ) : ℝ)|) ≤
        2 * (harmonic (m + 1) : ℝ) := by
  calc
    (∑ k ∈ Finset.range (m + 1),
        1 / |(m : ℝ) + 1 / 2 - ((m + 1 + k : ℕ) : ℝ)|) ≤
      ∑ k ∈ Finset.range (m + 1), 2 / ((k + 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have hdist :
            |(m : ℝ) + 1 / 2 - ((m + 1 + k : ℕ) : ℝ)| =
              (k : ℝ) + 1 / 2 := by
          rw [abs_of_nonpos]
          · push_cast
            ring
          · push_cast
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            linarith
        rw [hdist]
        have hden : 0 < (k : ℝ) + 1 / 2 := by positivity
        have hnat : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_div_iff₀ hden hnat]
        push_cast
        nlinarith
    _ = 2 * (harmonic (m + 1) : ℝ) :=
      sum_two_div_nat_succ_eq_two_mul_harmonic (m + 1)

/-- Both sides of a half-integer contribute at most two harmonic sums. -/
theorem sum_range_inv_abs_nat_add_half_le (m : ℕ) :
    (∑ n ∈ Finset.range (2 * m + 2),
      1 / |(m : ℝ) + 1 / 2 - (n : ℝ)|) ≤
        4 * (harmonic (m + 1) : ℝ) := by
  have hsplit : 2 * m + 2 = (m + 1) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  calc
    (∑ x ∈ Finset.range (m + 1),
          1 / |(m : ℝ) + 1 / 2 - (x : ℝ)|) +
        ∑ x ∈ Finset.range (m + 1),
          1 / |(m : ℝ) + 1 / 2 - ((m + 1 + x : ℕ) : ℝ)| ≤
      2 * (harmonic (m + 1) : ℝ) +
        2 * (harmonic (m + 1) : ℝ) :=
          add_le_add (left_half_distance_sum_le m)
            (right_half_distance_sum_le m)
    _ = 4 * (harmonic (m + 1) : ℝ) := by ring

end GafniTao
