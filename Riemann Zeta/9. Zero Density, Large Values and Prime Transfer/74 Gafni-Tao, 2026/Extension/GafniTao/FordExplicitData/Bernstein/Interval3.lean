import GafniTao.FordExplicitData.Bernstein.Interval3Coeff0
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff1
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff2
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff3
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff4
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff5
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff6
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff7
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff8
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff9
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff10
import GafniTao.FordExplicitData.Bernstein.Interval3Coeff11

namespace GafniTao

noncomputable section

theorem fordGapBernsteinSourceCoeff3
    {k : ℕ} (hk : k < 89) :
    polynomialBernsteinCoeff 88 fordGapAffineSource3 k =
      fordGapBernsteinCoeff3 k := by
  interval_cases k <;> simp

theorem fordGapAffine3_eq_bernstein :
    fordGapAffineSource3 = fordGapBernsteinExpansion3 := by
  rw [polynomial_eq_bernsteinExpansion 88
    fordGapAffineSource3 fordGapAffineSource3_natDegree_le]
  unfold polynomialBernsteinExpansion
  unfold fordGapBernsteinExpansion3
  apply Finset.sum_congr rfl
  intro k hk
  rw [fordGapBernsteinSourceCoeff3 (Finset.mem_range.mp hk)]

end

end GafniTao
