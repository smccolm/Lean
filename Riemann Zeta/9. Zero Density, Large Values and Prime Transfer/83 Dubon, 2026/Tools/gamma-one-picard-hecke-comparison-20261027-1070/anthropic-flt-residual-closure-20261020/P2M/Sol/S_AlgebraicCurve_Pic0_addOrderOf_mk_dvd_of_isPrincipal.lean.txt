import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Pic0_nsmul_mk_eq_zero_of_isPrincipal
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Pic0_addOrderOf_mk_dvd_of_isPrincipal

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ) (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : addOrderOf (Pic0.mk D) ∣ m :=
  addOrderOf_dvd_of_nsmul_eq_zero (AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal D m hD)
