import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Divisor_correspondence_correspondence

open AlgebraicCurve
theorem AlgebraicCurve.Divisor.correspondence_correspondence {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral) (huφ' : (u'.comp φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral) (hex : ∀ D : Divisor K F₂, Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) = Divisor.pushforwardAlong u hu (Divisor.pullbackAlong u' hu' D)) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Divisor_correspondence_correspondence.solution
