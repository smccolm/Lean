import GafniTao.FordExplicitData.Bernstein.Interval6Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval6Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff6
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource6 k =
      fordGapBernsteinCoeff6 k := by
  interval_cases k <;> simp

theorem fordGapAffine6_eq_bernstein :
    fordGapAffineSource6 = fordGapBernsteinExpansion6 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource6 fordGapAffineSource6_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion6
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff6 (Finset.mem_range.mp hk)]

end

end GafniTao
