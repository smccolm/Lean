import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts

open AlgebraicCurve

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts
    (K F F' E : Type*) [Field K] [Field F] [Field F'] [Field E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [IsAlgClosed E]
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (e : F →ₐ[K] E) (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.solution
