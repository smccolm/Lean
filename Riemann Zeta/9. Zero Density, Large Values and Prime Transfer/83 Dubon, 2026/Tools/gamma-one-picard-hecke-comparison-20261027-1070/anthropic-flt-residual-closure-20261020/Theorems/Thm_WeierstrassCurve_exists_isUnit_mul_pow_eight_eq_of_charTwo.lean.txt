import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo
    {M : Type u} [Field M] [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.solution
