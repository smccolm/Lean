import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ord_algebraMap_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.solution
