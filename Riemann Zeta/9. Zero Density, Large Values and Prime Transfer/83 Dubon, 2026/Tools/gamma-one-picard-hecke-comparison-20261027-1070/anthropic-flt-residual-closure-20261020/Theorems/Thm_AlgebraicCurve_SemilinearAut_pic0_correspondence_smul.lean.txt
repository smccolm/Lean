import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g') (c : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c) = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.solution
