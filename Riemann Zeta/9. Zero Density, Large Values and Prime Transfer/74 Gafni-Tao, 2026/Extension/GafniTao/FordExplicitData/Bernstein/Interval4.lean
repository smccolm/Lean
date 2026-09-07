import GafniTao.FordExplicitData.Bernstein.Interval4Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval4Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff4
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource4 k =
      fordGapBernsteinCoeff4 k := by
  interval_cases k <;> simp

theorem fordGapAffine4_eq_bernstein :
    fordGapAffineSource4 = fordGapBernsteinExpansion4 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource4 fordGapAffineSource4_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion4
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff4 (Finset.mem_range.mp hk)]

end

end GafniTao
