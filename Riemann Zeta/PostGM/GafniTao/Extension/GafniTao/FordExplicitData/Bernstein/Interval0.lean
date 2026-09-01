import GafniTao.FordExplicitData.Bernstein.Interval0Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval0Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff0
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource0 k =
      fordGapBernsteinCoeff0 k := by
  interval_cases k <;> simp

theorem fordGapAffine0_eq_bernstein :
    fordGapAffineSource0 = fordGapBernsteinExpansion0 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource0 fordGapAffineSource0_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion0
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff0 (Finset.mem_range.mp hk)]

end

end GafniTao
