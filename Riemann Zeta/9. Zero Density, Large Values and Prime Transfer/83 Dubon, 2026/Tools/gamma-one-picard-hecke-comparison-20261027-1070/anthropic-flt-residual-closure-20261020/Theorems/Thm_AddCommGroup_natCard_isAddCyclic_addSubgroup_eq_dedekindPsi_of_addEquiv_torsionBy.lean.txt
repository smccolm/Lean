import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy
    (n : ℕ) [NeZero n] {A : Type*} [AddCommGroup A]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.solution
