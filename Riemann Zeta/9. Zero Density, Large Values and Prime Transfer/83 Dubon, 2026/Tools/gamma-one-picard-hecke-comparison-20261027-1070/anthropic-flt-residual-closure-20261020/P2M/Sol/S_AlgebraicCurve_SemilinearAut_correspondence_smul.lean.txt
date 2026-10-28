import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pushforwardAlong_smul
import P2M.Util
namespace P2MW.S_AlgebraicCurve_SemilinearAut_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g') (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence φ ψ hφ hψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pullbackAlong_smul φ hφ hgφ, pushforwardAlong_smul ψ hψ hgψ]

end
