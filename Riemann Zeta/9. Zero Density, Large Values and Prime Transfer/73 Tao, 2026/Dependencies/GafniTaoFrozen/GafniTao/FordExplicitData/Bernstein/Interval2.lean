import GafniTao.FordExplicitData.Bernstein.Interval2Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval2Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff2
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource2 k =
      fordGapBernsteinCoeff2 k := by
  interval_cases k <;> simp

theorem fordGapAffine2_eq_bernstein :
    fordGapAffineSource2 = fordGapBernsteinExpansion2 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource2 fordGapAffineSource2_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion2
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff2 (Finset.mem_range.mp hk)]

end

end GafniTao
