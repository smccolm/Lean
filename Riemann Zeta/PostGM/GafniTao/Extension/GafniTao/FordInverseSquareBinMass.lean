import GafniTao.FordAdaptiveZeroBins
import GafniTao.FordKZeroSeries

/-!
# Summable inverse-square ordinate-bin masses

This is the translated lattice estimate required to sum Ford's nonlocal
zeros.  The logarithmic factor is evaluated at each bin's own height.
-/

open Complex Finset Filter Set
open scoped BigOperators Topology

namespace GafniTao

noncomputable section

private theorem ford_exp_two_le_eight : Real.exp 2 ≤ 8 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

noncomputable def fordInverseSquareBinDecay (n : ℤ) : ℝ :=
  1 / |(n : ℝ) + 1 / 2| ^ (2 : ℕ)

theorem summable_fordInverseSquareBinDecay :
    Summable fordInverseSquareBinDecay := by
  change Summable (fun n : ℤ => 1 / |(n : ℝ) + 1 / 2| ^ (2 : ℕ))
  have h := (Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr (by norm_num)
  exact h.congr (fun n => congrArg (fun q : ℝ => 1 / q)
    (Real.rpow_natCast |(n : ℝ) + 1 / 2| 2))

theorem fordInverseSquareBinDecay_nonneg (n : ℤ) :
    0 ≤ fordInverseSquareBinDecay n := by
  unfold fordInverseSquareBinDecay
  positivity

noncomputable def fordInverseSquareBinMass : ℝ :=
  ∑' n : ℤ, fordInverseSquareBinDecay n

theorem fordInverseSquareBinMass_nonneg :
    0 ≤ fordInverseSquareBinMass := by
  exact tsum_nonneg fordInverseSquareBinDecay_nonneg

noncomputable def fordInverseSquareBinLogWeight (n : ℤ) : ℝ :=
  fordInverseSquareBinDecay n *
    Real.log (fordAdaptiveZeroBinHeight n)

theorem fordAdaptiveZeroBinHeight_nat_eq
    {n : ℕ} (hn : 8 ≤ n) :
    fordAdaptiveZeroBinHeight (n : ℤ) = (n : ℝ) + 2 := by
  unfold fordAdaptiveZeroBinHeight
  simp only [Int.cast_natCast]
  have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_of_nonneg hnNonneg]
  have hEight : (8 : ℝ) ≤ n + 2 := by exact_mod_cast (show 8 ≤ n + 2 by omega)
  have hExp : Real.exp 2 ≤ (n : ℝ) + 2 :=
    ford_exp_two_le_eight.trans hEight
  rw [max_eq_right hEight, max_eq_right hExp]

theorem fordAdaptiveZeroBinHeight_neg_nat_eq
    {n : ℕ} (hn : 8 ≤ n) :
    fordAdaptiveZeroBinHeight (-(n : ℤ)) = (n : ℝ) + 2 := by
  unfold fordAdaptiveZeroBinHeight
  simp only [Int.cast_neg, Int.cast_natCast]
  have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_neg, abs_of_nonneg hnNonneg]
  have hEight : (8 : ℝ) ≤ n + 2 := by exact_mod_cast (show 8 ≤ n + 2 by omega)
  have hExp : Real.exp 2 ≤ (n : ℝ) + 2 :=
    ford_exp_two_le_eight.trans hEight
  rw [max_eq_right hEight, max_eq_right hExp]

theorem summable_fordInverseSquareBinLogWeight :
    Summable fordInverseSquareBinLogWeight := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · refine Summable.of_norm_bounded_eventually
      summable_ford_log_nat_add_two_div_sq ?_
    rw [Nat.cofinite_eq_atTop]
    refine Filter.eventually_atTop.2 ⟨8, ?_⟩
    intro n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold fordInverseSquareBinLogWeight fordInverseSquareBinDecay
      rw [fordAdaptiveZeroBinHeight_nat_eq hn]
      have hden : (n : ℝ) ^ 2 ≤ |(n : ℝ) + 1 / 2| ^ 2 := by
        rw [abs_of_pos (by positivity)]
        nlinarith
      simpa [div_eq_mul_inv, mul_comm] using
        div_le_div_of_nonneg_left hlog (by positivity) hden
    · exact mul_nonneg (fordInverseSquareBinDecay_nonneg _)
        (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
          (fordAdaptiveZeroBinHeight_ge_eight _)))
  · refine Summable.of_norm_bounded_eventually
      (summable_ford_log_nat_add_two_div_sq.mul_left 4) ?_
    rw [Nat.cofinite_eq_atTop]
    refine Filter.eventually_atTop.2 ⟨8, ?_⟩
    intro n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog : 0 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold fordInverseSquareBinLogWeight fordInverseSquareBinDecay
      rw [fordAdaptiveZeroBinHeight_neg_nat_eq hn]
      have hcast : ((-(n : ℤ) : ℤ) : ℝ) = -(n : ℝ) := by norm_num
      have habs : |((-(n : ℤ) : ℤ) : ℝ) + 1 / 2| =
          (n : ℝ) - 1 / 2 := by
        rw [hcast, abs_of_nonpos] <;> linarith
      rw [habs]
      have hden : (n : ℝ) ^ 2 / 4 ≤ ((n : ℝ) - 1 / 2) ^ 2 := by
        nlinarith [hnOne]
      have hdenPos : 0 < ((n : ℝ) - 1 / 2) ^ 2 := by
        exact sq_pos_of_pos (by linarith [hnOne])
      have hfrac : 1 / ((n : ℝ) - 1 / 2) ^ 2 ≤
          4 / (n : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hdenPos (sq_pos_of_pos hnPos)]
        nlinarith [hden]
      calc
        1 / ((n : ℝ) - 1 / 2) ^ 2 * Real.log ((n : ℝ) + 2) ≤
            (4 / (n : ℝ) ^ 2) * Real.log ((n : ℝ) + 2) := by
          exact mul_le_mul_of_nonneg_right hfrac hlog
        _ = 4 * (Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2) := by ring
    · exact mul_nonneg (fordInverseSquareBinDecay_nonneg _)
        (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
          (fordAdaptiveZeroBinHeight_ge_eight _)))

noncomputable def fordInverseSquareBinLogMass : ℝ :=
  ∑' n : ℤ, fordInverseSquareBinLogWeight n

theorem fordInverseSquareBinLogMass_nonneg :
    0 ≤ fordInverseSquareBinLogMass := by
  unfold fordInverseSquareBinLogMass
  exact tsum_nonneg (fun n => mul_nonneg
    (fordInverseSquareBinDecay_nonneg n)
    (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
      (fordAdaptiveZeroBinHeight_ge_eight n))))

theorem fordAdaptiveZeroBinHeight_le_mul
    (z a : ℤ) :
    fordAdaptiveZeroBinHeight z ≤
      fordAdaptiveZeroBinHeight a *
        fordAdaptiveZeroBinHeight (z - a) := by
  let Ha := fordAdaptiveZeroBinHeight a
  let Hn := fordAdaptiveZeroBinHeight (z - a)
  have hHaEight : (8 : ℝ) ≤ Ha := fordAdaptiveZeroBinHeight_ge_eight a
  have hHnEight : (8 : ℝ) ≤ Hn :=
    fordAdaptiveZeroBinHeight_ge_eight (z - a)
  have hHaOne : (1 : ℝ) ≤ Ha := by linarith
  have hHnOne : (1 : ℝ) ≤ Hn := by linarith
  have hAbsTriangle : |(z : ℝ)| ≤ |(a : ℝ)| + |((z - a : ℤ) : ℝ)| := by
    calc
      |(z : ℝ)| = |(a : ℝ) + ((z - a : ℤ) : ℝ)| := by
        congr 1
        push_cast
        ring
      _ ≤ |(a : ℝ)| + |((z - a : ℤ) : ℝ)| := abs_add_le _ _
  have hAbsProduct : |(z : ℝ)| + 2 ≤
      (|(a : ℝ)| + 2) * (|((z - a : ℤ) : ℝ)| + 2) := by
    have ha0 : 0 ≤ |(a : ℝ)| := abs_nonneg _
    have hn0 : 0 ≤ |((z - a : ℤ) : ℝ)| := abs_nonneg _
    nlinarith
  have hAbsToProduct : |(z : ℝ)| + 2 ≤ Ha * Hn := by
    exact hAbsProduct.trans (mul_le_mul
      (fordAdaptiveZeroBinHeight_ge_abs_add_two a)
      (fordAdaptiveZeroBinHeight_ge_abs_add_two (z - a))
      (by positivity) (by positivity))
  change max (Real.exp 2) (max 8 (|(z : ℝ)| + 2)) ≤ Ha * Hn
  apply max_le
  · exact (ford_exp_two_le_eight.trans hHaEight).trans
      (le_mul_of_one_le_right (by linarith) hHnOne)
  · apply max_le
    · exact hHaEight.trans
        (le_mul_of_one_le_right (by linarith) hHnOne)
    · exact hAbsToProduct

theorem log_fordAdaptiveZeroBinHeight_le_add
    (z a : ℤ) :
    Real.log (fordAdaptiveZeroBinHeight z) ≤
      Real.log (fordAdaptiveZeroBinHeight a) +
        Real.log (fordAdaptiveZeroBinHeight (z - a)) := by
  have hza := fordAdaptiveZeroBinHeight_le_mul z a
  have hzPos : 0 < fordAdaptiveZeroBinHeight z :=
    lt_of_lt_of_le (by norm_num) (fordAdaptiveZeroBinHeight_ge_eight z)
  have haPos : 0 < fordAdaptiveZeroBinHeight a :=
    lt_of_lt_of_le (by norm_num) (fordAdaptiveZeroBinHeight_ge_eight a)
  have hnPos : 0 < fordAdaptiveZeroBinHeight (z - a) :=
    lt_of_lt_of_le (by norm_num) (fordAdaptiveZeroBinHeight_ge_eight (z - a))
  calc
    Real.log (fordAdaptiveZeroBinHeight z) ≤
        Real.log (fordAdaptiveZeroBinHeight a *
          fordAdaptiveZeroBinHeight (z - a)) :=
      Real.strictMonoOn_log.monotoneOn hzPos (mul_pos haPos hnPos) hza
    _ = Real.log (fordAdaptiveZeroBinHeight a) +
        Real.log (fordAdaptiveZeroBinHeight (z - a)) := by
      rw [Real.log_mul haPos.ne' hnPos.ne']

theorem tsum_fordInverseSquareBinDecay_sub (a : ℤ) :
    (∑' z : ℤ, fordInverseSquareBinDecay (z - a)) =
      fordInverseSquareBinMass := by
  unfold fordInverseSquareBinMass
  simpa using (Equiv.subRight a).tsum_eq fordInverseSquareBinDecay

theorem tsum_fordInverseSquareBinLogWeight_sub (a : ℤ) :
    (∑' z : ℤ, fordInverseSquareBinLogWeight (z - a)) =
      fordInverseSquareBinLogMass := by
  unfold fordInverseSquareBinLogMass
  simpa using (Equiv.subRight a).tsum_eq fordInverseSquareBinLogWeight

/-- Uniform translated lattice bound, retaining exactly one logarithm at the
physical centre. -/
theorem sum_fordInverseSquareBinDecay_mul_adaptiveLog_le
    (bins : Finset ℤ) (a : ℤ) :
    ∑ z ∈ bins, fordInverseSquareBinDecay (z - a) *
        Real.log (fordAdaptiveZeroBinHeight z) ≤
      Real.log (fordAdaptiveZeroBinHeight a) *
          fordInverseSquareBinMass +
        fordInverseSquareBinLogMass := by
  have hlogA : 0 ≤ Real.log (fordAdaptiveZeroBinHeight a) :=
    Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
      (fordAdaptiveZeroBinHeight_ge_eight a))
  calc
    ∑ z ∈ bins, fordInverseSquareBinDecay (z - a) *
        Real.log (fordAdaptiveZeroBinHeight z) ≤
      ∑ z ∈ bins, fordInverseSquareBinDecay (z - a) *
        (Real.log (fordAdaptiveZeroBinHeight a) +
          Real.log (fordAdaptiveZeroBinHeight (z - a))) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left
        (log_fordAdaptiveZeroBinHeight_le_add z a)
        (fordInverseSquareBinDecay_nonneg _)
    _ = Real.log (fordAdaptiveZeroBinHeight a) *
          (∑ z ∈ bins, fordInverseSquareBinDecay (z - a)) +
        ∑ z ∈ bins, fordInverseSquareBinLogWeight (z - a) := by
      unfold fordInverseSquareBinLogWeight
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      ring
    _ ≤ Real.log (fordAdaptiveZeroBinHeight a) *
          fordInverseSquareBinMass + fordInverseSquareBinLogMass := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hlogA
        have hs := summable_fordInverseSquareBinDecay.comp_injective
          (Equiv.subRight a).injective
        exact (hs.sum_le_tsum bins (fun z _ =>
          fordInverseSquareBinDecay_nonneg _)).trans_eq
            (tsum_fordInverseSquareBinDecay_sub a)
      · have hs := summable_fordInverseSquareBinLogWeight.comp_injective
          (Equiv.subRight a).injective
        exact (hs.sum_le_tsum bins (fun z _ => mul_nonneg
          (fordInverseSquareBinDecay_nonneg _)
          (Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 8).trans
            (fordAdaptiveZeroBinHeight_ge_eight _))))).trans_eq
              (tsum_fordInverseSquareBinLogWeight_sub a)

#print axioms summable_fordInverseSquareBinLogWeight
#print axioms sum_fordInverseSquareBinDecay_mul_adaptiveLog_le

end

end GafniTao
