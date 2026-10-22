import Dubon2026.SourceOriginalEllipticCoordinate

/-! DUB-17/18 -> original torsion cardinality -> compatible complex
place charts. Away from its pole, the explicit inverse elliptic coordinate
is analytic with nonzero derivative. This permits the center-order result
to be transported to nearby points by native analytic inversion.+-/
namespace Dubon2026.SourceFunctionField.EllipticCoordinate
noncomputable section
open UpperHalfPlane
open scoped ComplexConjugate

theorem analyticAt_param_of_ne_one (τ : ℍ) {u : ℂ} (hu : u ≠ 1) :
    AnalyticAt ℂ (param τ) u := by
  unfold param
  exact (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hu.symm)

theorem hasDerivAt_param_of_ne_one (τ : ℍ) {u : ℂ} (hu : u ≠ 1) :
    HasDerivAt (param τ) (((τ : ℂ) - conj (τ : ℂ)) / (1 - u) ^ 2) u := by
  have h := ((hasDerivAt_const u (τ : ℂ)).sub
    ((hasDerivAt_id u).mul_const (conj (τ : ℂ)))).div
      ((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id u)) (sub_ne_zero.mpr hu.symm)
  convert h using 1
  dsimp only [Pi.sub_apply, id_eq]
  congr 1
  ring

theorem deriv_param_ne_zero_of_ne_one (τ : ℍ) {u : ℂ} (hu : u ≠ 1) :
    deriv (param τ) u ≠ 0 := by
  rw [(hasDerivAt_param_of_ne_one τ hu).deriv]
  exact div_ne_zero (sub_ne_zero.mpr (upper_ne_conj τ τ))
    (pow_ne_zero 2 (sub_ne_zero.mpr hu.symm))

end
end Dubon2026.SourceFunctionField.EllipticCoordinate
