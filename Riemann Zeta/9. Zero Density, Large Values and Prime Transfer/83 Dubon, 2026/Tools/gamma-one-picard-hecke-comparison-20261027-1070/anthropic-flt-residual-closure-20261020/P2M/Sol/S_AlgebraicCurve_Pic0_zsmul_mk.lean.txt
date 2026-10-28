import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_zsmul_mk

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (m : ℤ) (D : Divisor.degZero (K := K) (F := F)) : m • Pic0.mk D = Pic0.mk (m • D) :=
  (map_zsmul (QuotientAddGroup.mk' _) m D).symm
