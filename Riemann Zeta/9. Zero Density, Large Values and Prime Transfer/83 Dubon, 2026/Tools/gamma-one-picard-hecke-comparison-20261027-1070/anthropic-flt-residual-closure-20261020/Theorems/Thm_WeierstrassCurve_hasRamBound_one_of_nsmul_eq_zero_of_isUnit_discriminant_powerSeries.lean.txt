import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
attribute [-instance] instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] WeierstrassCurve.reducePoint_zero FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

theorem WeierstrassCurve.hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries
    (E : WeierstrassCurve (PowerSeries (AlgebraicClosure ℚ))) (hΔ : IsUnit E.Δ) {d : ℕ} (hd : 0 < d)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))] (x y : HahnSeries ℚ (AlgebraicClosure ℚ))
    (h : (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Nonsingular x y)
    (htor : d • (WeierstrassCurve.Affine.Point.some x y h :
      (E.map (HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ))).toAffine.Point) = 0) :
    HahnSeries.HasRamBound 1 x ∧ HahnSeries.HasRamBound 1 y := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasRamBound_one_of_nsmul_eq_zero_of_isUnit_discriminant_powerSeries.solution
