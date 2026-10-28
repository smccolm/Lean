import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_deuring_of_isUnit_three
    {M : Type u} [Field M] [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.solution
