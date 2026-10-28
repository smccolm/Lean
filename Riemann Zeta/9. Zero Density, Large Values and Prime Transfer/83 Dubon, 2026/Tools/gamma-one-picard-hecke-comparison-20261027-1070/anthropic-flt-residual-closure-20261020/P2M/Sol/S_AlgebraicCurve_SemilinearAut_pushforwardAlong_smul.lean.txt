import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforward_smul
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hgg' : IntertwinesAlong φ.toRingHom g g') (D : Divisor K F') : Divisor.pushforwardAlong φ hφ (g' • D) = g • Divisor.pushforwardAlong φ hφ D := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact pushforward_smul hgg' D

end
