import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_pushforward_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [smul_single, Divisor.pushforward_single, Divisor.pushforward_single, smul_single,
      restrict_smul hgg' w, inertiaDeg_smul hgg' w]

end
