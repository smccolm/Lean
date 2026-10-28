import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_mk_eq_zero_iff

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  exact Divisor.mem_principal
