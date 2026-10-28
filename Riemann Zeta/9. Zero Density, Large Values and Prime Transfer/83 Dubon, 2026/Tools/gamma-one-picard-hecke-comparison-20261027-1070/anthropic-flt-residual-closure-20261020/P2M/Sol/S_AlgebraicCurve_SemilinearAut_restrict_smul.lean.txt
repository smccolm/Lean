import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_restrict_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).restrict F = g • (w.restrict F) := by
  apply Place.toValuationSubring_injective
  rw [Place.restrict_toValuationSubring, smul_toValuationSubring, smul_toValuationSubring,
    Place.restrict_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
    hgg'.inv x]

end
