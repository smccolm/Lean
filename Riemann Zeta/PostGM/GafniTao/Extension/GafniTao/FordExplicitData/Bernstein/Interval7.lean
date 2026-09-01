import GafniTao.FordExplicitData.Bernstein.Interval7Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval7Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff7
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource7 k =
      fordGapBernsteinCoeff7 k := by
  interval_cases k <;> simp

theorem fordGapAffine7_eq_bernstein :
    fordGapAffineSource7 = fordGapBernsteinExpansion7 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource7 fordGapAffineSource7_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion7
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff7 (Finset.mem_range.mp hk)]

end

end GafniTao
