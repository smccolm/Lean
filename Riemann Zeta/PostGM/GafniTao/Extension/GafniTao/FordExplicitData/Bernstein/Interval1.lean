import GafniTao.FordExplicitData.Bernstein.Interval1Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval1Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff1
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource1 k =
      fordGapBernsteinCoeff1 k := by
  interval_cases k <;> simp

theorem fordGapAffine1_eq_bernstein :
    fordGapAffineSource1 = fordGapBernsteinExpansion1 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource1 fordGapAffineSource1_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion1
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff1 (Finset.mem_range.mp hk)]

end

end GafniTao
