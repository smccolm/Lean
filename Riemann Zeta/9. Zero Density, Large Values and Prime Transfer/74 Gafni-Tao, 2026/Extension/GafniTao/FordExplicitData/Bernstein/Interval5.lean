import GafniTao.FordExplicitData.Bernstein.Interval5Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval5Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff5
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource5 k =
      fordGapBernsteinCoeff5 k := by
  interval_cases k <;> simp

theorem fordGapAffine5_eq_bernstein :
    fordGapAffineSource5 = fordGapBernsteinExpansion5 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource5 fordGapAffineSource5_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion5
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff5 (Finset.mem_range.mp hk)]

end

end GafniTao
