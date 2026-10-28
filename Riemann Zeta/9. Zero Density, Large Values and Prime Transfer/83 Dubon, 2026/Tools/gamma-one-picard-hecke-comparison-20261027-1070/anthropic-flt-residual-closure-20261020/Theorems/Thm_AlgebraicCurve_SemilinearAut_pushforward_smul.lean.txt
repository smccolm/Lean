import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_pushforward_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pushforward_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_pushforward_smul.solution
