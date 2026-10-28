import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

theorem WeierstrassCurve.exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one
    {L : Type*} [Field L] [DecidableEq L] [Algebra ℚ L] [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (p : ℕ) (hp : p.Prime) :
    ∃ T : (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine.Point, addOrderOf T = p ∧
      ∀ k : ℕ, ¬ HEq (WeierstrassCurve.Affine.Point.vcInvFun (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange L)
        (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve L).toAffine T) (k • T) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_addOrderOf_eq_and_vcInvFun_ne_nsmul_of_sq_eq_neg_one.solution
