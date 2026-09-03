import GafniTao.PintzErrorParameters

/-!
# The contour error on the physical zero set

The uniform contour estimate is specialized here to every member of the
actual multiplicity-bearing high-zero set.  In particular, the `hError`
parameter in the finite Pintz density inequality is discharged from the
Vinogradov--Korobov range and the explicit height threshold.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz_physical_contour_error_le_quarter
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hT : pintzContourErrorHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    ∀ rho ∈ pintzHighZeroSet eta T (pintzDensityLambda eta T),
      pintzEquation46ErrorBound (1 - rho.re) rho.im
          (pintzDensityLambda eta T)
          (pintzPhysicalZetaMajorant eta T)
          (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4 := by
  intro rho hrho
  have hrhoZero : rho ∈ zeroSet (1 - eta) T :=
    pintzHighZeroSet_subset eta T (pintzDensityLambda eta T) hrho
  have hdata := mem_zeroSet_data hrhoZero
  have hrhoHalf : 1 / 2 ≤ rho.re := by
    linarith
  have hlambdaPos : 0 < pintzDensityLambda eta T := by
    have hbase : Real.exp (Real.exp 1) ≤ T := by
      unfold pintzContourErrorHeight at hT
      exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hT
    exact pintzDensityLambda_pos heta.le
      ((Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hbase)
  have huniform := pintzEquation46ErrorBound_le_uniform
    (etaJ := 1 - rho.re) (gamma := rho.im)
    (lambda := pintzDensityLambda eta T)
    (Z := pintzPhysicalZetaMajorant eta T)
    (by simpa [pintzRho] using hrhoHalf) hlambdaPos
  exact huniform.trans
    (pintz_uniform_contour_error_le_quarter hc heta hetaUpper hT hetaAbove)

#print axioms pintz_physical_contour_error_le_quarter

end

end GafniTao
