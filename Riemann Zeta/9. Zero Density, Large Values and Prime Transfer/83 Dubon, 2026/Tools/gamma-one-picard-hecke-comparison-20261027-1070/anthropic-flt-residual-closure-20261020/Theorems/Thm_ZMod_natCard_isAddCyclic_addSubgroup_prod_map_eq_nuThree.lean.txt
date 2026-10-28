import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree

open ModularCurve
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) + τ v + v = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuThree n := by p2m_exact_reverting @_root_.P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree.solution
