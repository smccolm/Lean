import Mathlib
import Definitions.Def_WeierstrassCurve_CyclicQuotientJ
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two

open WeierstrassCurve

universe u in

theorem WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : L) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q (ℓ / 2)) x)
          (E.veluY (E.oddOrderSummingSet Q (ℓ / 2)) x y) h') :
    (⟨E.stepCurve H ℓ, E.stepSubgroup H ℓ⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.solution
