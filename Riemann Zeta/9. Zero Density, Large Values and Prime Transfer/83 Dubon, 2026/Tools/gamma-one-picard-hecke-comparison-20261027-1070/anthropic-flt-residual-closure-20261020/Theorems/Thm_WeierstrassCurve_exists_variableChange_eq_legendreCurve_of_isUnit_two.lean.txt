import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two
    {M : Type u} [Field M] (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two.solution
