import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_exists_torsionBy_reduction_addEquiv
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec
attribute [-simp] compl₂EDS_two

open ModularCurve.TatePoint
open scoped Classical
theorem ModularCurve.B3.exists_torsionBy_reduction_addEquiv (W : WeierstrassCurve H)
    [W.IsElliptic] (hW : IntegralCoeffs W) (hΔ : W.Δ.orderTop = 0)
    [(specialFibre W).IsElliptic] (p : ℕ) [Fact p.Prime] :
    ∃ e : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ) ≃+
        Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ),
      ∀ (P : Submodule.torsionBy ℤ W.toAffine.Point (p : ℤ)) (x y : H)
        (h : W.toAffine.Nonsingular x y),
        (P : W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x y h →
          ∃ h₀ : (specialFibre W).toAffine.Nonsingular (x.coeff 0) (y.coeff 0),
            ((e P : Submodule.torsionBy ℤ (specialFibre W).toAffine.Point (p : ℤ)) :
                (specialFibre W).toAffine.Point) =
              WeierstrassCurve.Affine.Point.some (x.coeff 0) (y.coeff 0) h₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_exists_torsionBy_reduction_addEquiv.solution
