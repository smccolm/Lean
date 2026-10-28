import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_genusFF_eq_of_algEquiv

open AlgebraicCurve

theorem AlgebraicCurve.genusFF_eq_of_algEquiv
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    (e : F₁ ≃ₐ[K] F₂) :
    genusFF K F₁ = genusFF K F₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_genusFF_eq_of_algEquiv.solution
