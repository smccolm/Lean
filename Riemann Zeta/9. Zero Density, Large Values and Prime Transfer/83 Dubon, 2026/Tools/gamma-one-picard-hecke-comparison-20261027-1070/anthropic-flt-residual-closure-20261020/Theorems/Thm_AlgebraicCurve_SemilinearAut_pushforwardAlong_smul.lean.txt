import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pushforwardAlong_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F') : Divisor.pushforwardAlong φ hφ (g' • D) = g • Divisor.pushforwardAlong φ hφ D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul.solution
