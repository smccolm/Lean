import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluPointMap2
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.stepCurve_stepSubgroup_two_eq
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L) (h2 : (2 : L) ≠ 0)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    {x₀ y₀ : L} (hns : E.toAffine.Nonsingular x₀ y₀) (hQH : (.some x₀ y₀ hns : E.toAffine.Point) ∈ H)
    (hgy : E.veluGy x₀ y₀ = 0) (hΔ : (E.veluQuotient2 x₀ y₀).Δ ≠ 0)
    (φ : E.toAffine.Point →+ (E.veluQuotient2 x₀ y₀).toAffine.Point)
    (hφ : ⇑φ = veluPointMap2 h2 hns.1 hgy hΔ) :
    (⟨E.stepCurve H 2, E.stepSubgroup H 2⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient2 x₀ y₀, H.map φ⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_two_eq.solution
