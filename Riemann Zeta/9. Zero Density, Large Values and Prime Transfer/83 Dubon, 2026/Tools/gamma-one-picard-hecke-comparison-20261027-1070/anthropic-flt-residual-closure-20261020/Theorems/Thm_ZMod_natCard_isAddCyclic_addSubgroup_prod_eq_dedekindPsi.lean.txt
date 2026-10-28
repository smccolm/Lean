import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n} = ModularCurve.dedekindPsi n := by p2m_exact_reverting @_root_.P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.solution
