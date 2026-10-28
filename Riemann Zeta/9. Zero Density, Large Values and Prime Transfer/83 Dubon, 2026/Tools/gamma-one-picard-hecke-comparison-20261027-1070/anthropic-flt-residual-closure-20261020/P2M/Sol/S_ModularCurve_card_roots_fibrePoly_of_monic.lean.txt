import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import P2M.Util
namespace P2MW.S_ModularCurve_card_roots_fibrePoly_of_monic

open Polynomial ModularCurve

theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (a : K) :
    Multiset.card (fibrePoly Φ a).roots = Φ.natDegree := by
  rw [← (IsAlgClosed.splits (fibrePoly Φ a)).natDegree_eq_card_roots]
  exact hΦ.natDegree_map _
