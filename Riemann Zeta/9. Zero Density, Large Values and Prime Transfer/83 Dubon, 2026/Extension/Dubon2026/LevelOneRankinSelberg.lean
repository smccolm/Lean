import Dubon2026.RankinConvolutionThreeFifths
import Dubon2026.RankinDeconvolutionRemainder

/-! # The unconditional full-level Rankin--Selberg three-fifths remainder -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open scoped Topology

noncomputable section

/-- For every genuine full-level cusp form of weight at least two, the original normalized square sum has the exact three-fifths error and actual Petersson main term. -/
theorem exists_level_one_cusp_square_three_fifths {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      |squareSummatory (normalizedCuspCoefficients f) x - cuspRankinResidue f * x| ≤ C * x ^ (3 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_level_one_rankinConvolution_three_fifths f hk
  exact exists_cusp_square_remainder_of_rankinConvolution f (by omega) hC.le hb

/-- The actual full-level normalized cusp coefficients satisfy the literal Rankin--Selberg O_f(x^(3/5)) asymptotic. -/
theorem level_one_cusp_square_three_fifths_remainder {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) :
    (fun x : ℝ => squareSummatory (normalizedCuspCoefficients f) x - cuspRankinResidue f * x)
      =O[atTop] (fun x : ℝ => x ^ (3 / 5 : ℝ)) := by
  obtain ⟨C, _, hb⟩ := exists_level_one_cusp_square_three_fifths f hk
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hb x hx

/-- The exact full-level source mean-square asymptotic includes the strict positivity of its genuine residue for every nonzero form. -/
theorem level_one_rankin_selberg {k : ℤ}
    (f : CuspForm ((Gamma0 1).map (mapGL ℝ)) k) (hk : 2 ≤ k) (hf : f ≠ 0) :
    0 < cuspRankinResidue f ∧
      (fun x : ℝ => (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖normalizedCuspCoefficients f n‖ ^ 2) - cuspRankinResidue f * x)
        =O[atTop] (fun x : ℝ => x ^ (3 / 5 : ℝ)) :=
  ⟨cuspRankinResidue_pos f (by omega) hf, level_one_cusp_square_three_fifths_remainder f hk⟩

end
end Dubon2026
