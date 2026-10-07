import Dubon2026.RankinRieszDifferenceEstimate

/-! # The exact full-level Rankin convolution summatory error -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped Topology

noncomputable section

/-- Actual forward and backward Riesz bounds give the exact three-fifths error for the unsmoothed full-level Rankin convolution. -/
theorem exists_level_one_rankinConvolution_three_fifths_large {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 32 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
        C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_rankinConvolutionRieszError_three_fifths_bound f hk
  refine ⟨|rankinConvolutionResidue f| + C, by positivity, ?_⟩
  intro x hx
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hh : 0 < x ^ (3 / 5 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hscale := rieszOptimization_scale_le_quarter hx
  have hforward := hb x x hx1 hx0 le_rfl (by linarith)
  have hbackward := hb x (x - 2 * x ^ (3 / 5 : ℝ)) hx1 (by linarith) (by linarith) (by linarith)
  have hmax : max
      |rieszSecondDifference (rankinConvolutionRieszError f) x (x ^ (3 / 5 : ℝ))|
      |rieszSecondDifference (rankinConvolutionRieszError f) (x - 2 * x ^ (3 / 5 : ℝ)) (x ^ (3 / 5 : ℝ))| /
      (x ^ (3 / 5 : ℝ)) ^ 2 ≤ C * x ^ (3 / 5 : ℝ) := by
    rw [div_le_iff₀ (sq_pos_of_pos hh)] at hforward hbackward ⊢
    exact max_le hforward hbackward
  have hr := rankinConvolution_error_le_riesz f x hh
  have hc := mul_le_mul_of_nonneg_right (le_abs_self (rankinConvolutionResidue f)) hh.le
  exact hr.trans ((add_le_add hc hmax).trans_eq (by ring))

/-- Enlarging the constant on the actual finite initial range gives the full-level convolution estimate for every x at least one. -/
theorem exists_level_one_rankinConvolution_three_fifths {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤
        C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_level_one_rankinConvolution_three_fifths_large f hk
  obtain ⟨B, hB, hsum⟩ := exists_rankinConvolution_sum_upper f (by omega)
  let D := (B + |rankinConvolutionResidue f|) * 32
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D, by positivity, ?_⟩
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  have hp : 0 ≤ x ^ (3 / 5 : ℝ) := Real.rpow_nonneg hx0 _
  by_cases hx32 : 32 ≤ x
  · exact (hb x hx32).trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + D) hp)
  · have hx32' : x ≤ 32 := le_of_lt (lt_of_not_ge hx32)
    have hs0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re :=
      Finset.sum_nonneg (fun n _ => rankinConvolutionCoefficients_re_nonneg f n)
    have hs : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) ≤ B * x :=
      (hsum ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left (Nat.floor_le hx0) hB.le)
    have he := abs_sub (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re)
      (rankinConvolutionResidue f * x)
    rw [abs_of_nonneg hs0, abs_mul, abs_of_nonneg hx0] at he
    have hbD : |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) - rankinConvolutionResidue f * x| ≤ D := by
      apply he.trans
      calc
        _ ≤ B * x + |rankinConvolutionResidue f| * x := by linarith
        _ = (B + |rankinConvolutionResidue f|) * x := by ring
        _ ≤ D := mul_le_mul_of_nonneg_left hx32' (by positivity)
    have hpow : 1 ≤ x ^ (3 / 5 : ℝ) := Real.one_le_rpow hx (by norm_num)
    exact (hbD.trans (by linarith : D ≤ C + D)).trans
      (le_mul_of_one_le_right (by positivity) hpow)

/-- The original full-level convolution has the literal O(x^(3/5)) summatory remainder. -/
theorem level_one_rankinConvolution_remainder {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (rankinConvolutionCoefficients f n).re) -
      rankinConvolutionResidue f * x) =O[atTop] (fun x : ℝ => x ^ (3 / 5 : ℝ)) := by
  obtain ⟨C, _, hb⟩ := exists_level_one_rankinConvolution_three_fifths f hk
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hb x hx

end
end Dubon2026
