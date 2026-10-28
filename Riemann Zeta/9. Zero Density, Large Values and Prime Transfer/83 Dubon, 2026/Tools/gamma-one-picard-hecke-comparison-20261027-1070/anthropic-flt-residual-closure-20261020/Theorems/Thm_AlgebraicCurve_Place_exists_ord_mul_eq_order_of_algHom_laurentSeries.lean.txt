import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
attribute [-simp] HahnSeries.ramScale_apply

open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.solution
