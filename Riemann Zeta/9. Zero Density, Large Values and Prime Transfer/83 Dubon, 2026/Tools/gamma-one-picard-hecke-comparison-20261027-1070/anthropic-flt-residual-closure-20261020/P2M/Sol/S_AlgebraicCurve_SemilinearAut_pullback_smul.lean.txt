import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_pullback_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F) : Divisor.pullback F' (g • D) = g' • Divisor.pullback F' D := by
  ext w
  rw [Divisor.pullback_apply, divisor_smul_apply, divisor_smul_apply, Divisor.pullback_apply,
    restrict_smul hgg'.inv w, ramificationIndex_smul hgg'.inv w]

end
