import GafniTao.FordExplicitData.PositiveFactor

/-!
# Explicit exact polynomial certificates

The exact rational data are sharded into small modules so that Lean can
kernel-check and cache each block.  No generated coefficient is trusted:
the source-identification theorems are proved in the consumer module.
-/

namespace GafniTao

noncomputable section

set_option maxRecDepth 100000000

set_option maxHeartbeats 0 in
theorem fordNegativeUpperPolynomial_eq_explicit :
    fordNegativeUpperPolynomial = fordNegativeUpperExplicit := by
  apply Polynomial.funext
  intro v
  apply Polynomial.funext
  intro y
  norm_num [fordNegativeUpperPolynomial, fordScaledTaylorPolynomial,
    fordNegativePhasePolynomial, fordBiRat, fordBiY, fordBiV,
    fordNegativeUpperExplicit, Finset.sum_range_succ,
    fordNegativeUpperBlock0, fordNegativeUpperBlock1, fordNegativeUpperBlock2, fordNegativeUpperCoeff0, fordNegativeUpperCoeff1, fordNegativeUpperCoeff2, fordNegativeUpperCoeff3, fordNegativeUpperCoeff4, fordNegativeUpperCoeff5, fordNegativeUpperCoeff6, fordNegativeUpperCoeff7, fordNegativeUpperCoeff8, fordNegativeUpperCoeff9, fordNegativeUpperCoeff10, fordNegativeUpperCoeff11, fordNegativeUpperCoeff12, fordNegativeUpperCoeff13, fordNegativeUpperCoeff14, fordNegativeUpperCoeff15, fordNegativeUpperCoeff16, fordNegativeUpperCoeff17, fordNegativeUpperCoeff18, fordNegativeUpperCoeff19, fordNegativeUpperCoeff20, fordNegativeUpperCoeff21, fordNegativeUpperCoeff22, fordNegativeUpperCoeff23, fordNegativeUpperCoeff24, fordNegativeUpperCoeff25, fordNegativeUpperCoeff26, fordNegativeUpperCoeff27, fordNegativeUpperCoeff28, fordNegativeUpperCoeff29, fordNegativeUpperCoeff30, fordNegativeUpperCoeff31, fordNegativeUpperCoeff32, fordNegativeUpperCoeff33, fordNegativeUpperCoeff34, fordNegativeUpperCoeff35, fordNegativeUpperCoeff36, fordNegativeUpperCoeff37, fordNegativeUpperCoeff38, fordNegativeUpperCoeff39, fordNegativeUpperCoeff40, fordNegativeUpperCoeff41, fordNegativeUpperCoeff42, fordNegativeUpperCoeff43, fordNegativeUpperCoeff44, fordNegativeUpperCoeff45, fordNegativeUpperCoeff46, fordNegativeUpperCoeff47, fordNegativeUpperCoeff48, fordNegativeUpperCoeff49, fordNegativeUpperCoeff50, fordNegativeUpperCoeff51, fordNegativeUpperCoeff52, fordNegativeUpperCoeff53, fordNegativeUpperCoeff54]
  ring

end

end GafniTao
