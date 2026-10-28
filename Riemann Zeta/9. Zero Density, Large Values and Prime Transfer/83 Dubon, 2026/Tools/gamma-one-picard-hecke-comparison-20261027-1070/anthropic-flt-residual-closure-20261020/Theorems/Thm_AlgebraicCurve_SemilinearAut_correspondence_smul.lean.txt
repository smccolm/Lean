import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g') (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence φ ψ hφ hψ D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_correspondence_smul.solution
