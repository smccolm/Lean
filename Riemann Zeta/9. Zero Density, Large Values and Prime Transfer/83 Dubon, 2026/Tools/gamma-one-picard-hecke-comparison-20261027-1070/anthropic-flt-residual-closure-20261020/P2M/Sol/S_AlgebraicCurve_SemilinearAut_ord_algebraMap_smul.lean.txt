import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by
  have hrw : algebraMap F F' f = g' • (algebraMap F F' (g⁻¹ • f)) := by
    rw [hgg' (g⁻¹ • f), smul_inv_smul]
  rw [hrw]
  exact ord_smul g' w _

end
