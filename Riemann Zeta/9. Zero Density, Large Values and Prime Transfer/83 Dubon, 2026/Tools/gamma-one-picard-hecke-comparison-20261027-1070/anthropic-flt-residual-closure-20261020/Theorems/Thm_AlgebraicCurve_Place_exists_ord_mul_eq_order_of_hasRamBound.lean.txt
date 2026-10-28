import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_HahnSeries_RamificationBound
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound

theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_hasRamBound
    {K L F : Type*} [Field K] [Field L] [Algebra K L] [Field F] [Algebra K F]
    (φ : F →ₐ[K] HahnSeries ℚ L) {d : ℕ} (hd : 0 < d)
    (hφ : ∀ x : F, HahnSeries.HasRamBound d (φ x))
    (hnt : ∃ x : F, (φ x).order ≠ 0) :
    ∃ (w : AlgebraicCurve.Place K F) (g : ℚ), 0 < g ∧
      ∀ x : F, (w.ord x : ℚ) * g = (φ x).order := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_hasRamBound.solution
