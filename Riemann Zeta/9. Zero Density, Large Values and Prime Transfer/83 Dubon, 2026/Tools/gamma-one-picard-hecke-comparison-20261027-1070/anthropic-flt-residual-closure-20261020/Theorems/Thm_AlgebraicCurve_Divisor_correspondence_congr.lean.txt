import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_correspondence_congr

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.correspondence_congr {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁] [HasPrincipalDivisors K F₁] {φ ψ φ' ψ' : F →ₐ[K] F₁} (hφeq : φ = φ') (hψeq : ψ = ψ') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ D = Divisor.correspondence φ' ψ' hφ' hψ' D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_correspondence_congr.solution
