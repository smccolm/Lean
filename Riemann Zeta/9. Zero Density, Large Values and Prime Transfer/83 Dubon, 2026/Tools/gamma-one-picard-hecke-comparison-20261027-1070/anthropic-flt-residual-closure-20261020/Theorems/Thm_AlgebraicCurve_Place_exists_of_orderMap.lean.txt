import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_of_orderMap

theorem AlgebraicCurve.Place.exists_of_orderMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (μ : F → WithTop ℤ) (h_top : ∀ x, μ x = ⊤ ↔ x = 0)
    (h_mul : ∀ x y, μ (x * y) = μ x + μ y) (h_add : ∀ x y, min (μ x) (μ y) ≤ μ (x + y))
    (h_const : ∀ c : K, c ≠ 0 → μ (algebraMap K F c) = 0) (h_nontriv : ∃ x, 0 < μ x ∧ μ x ≠ ⊤) :
    ∃ (P : AlgebraicCurve.Place K F) (e : ℕ), 0 < e ∧
      (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ μ x) ∧
      ∀ x, x ≠ 0 → μ x = (((e : ℤ) * P.ord x : ℤ) : WithTop ℤ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_of_orderMap.solution
