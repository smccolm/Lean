import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq

set_option autoImplicit false

p2m_open "AlgebraicCurve~mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor"

theorem AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)))
    (M₀ d g₀ : ℕ)
    (hell : ∀ N, M₀ ≤ N → (ell (N • D) : ℤ) = N * d + 1 - g₀)
    (m : ℕ) (hm : M₀ + 1 ≤ m) :
    (LSpace ((m + 1) • D) : Submodule K F)
      ≤ LSpace (m • D) ⊔ (LSpace (m • D)).map (LinearMap.mulLeft K x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq.solution
