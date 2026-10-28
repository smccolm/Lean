import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (m : ℕ) :
    (∀ g ∈ LSpace ((m : ℕ) • D), x * g ∈ LSpace ((m + 1) • D)) ∧
    (∀ g ∈ LSpace ((m + 1) • D), x * g ∈ LSpace ((m + 1) • D) → g ∈ LSpace (m • D)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor.solution
