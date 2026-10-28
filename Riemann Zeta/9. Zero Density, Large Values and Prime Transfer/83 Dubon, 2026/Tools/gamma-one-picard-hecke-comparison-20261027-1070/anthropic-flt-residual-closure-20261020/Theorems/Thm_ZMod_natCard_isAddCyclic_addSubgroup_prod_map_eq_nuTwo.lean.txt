import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo

open ModularCurve
theorem ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo (n : ℕ) [NeZero n]
    (τ : ZMod n × ZMod n →+ ZMod n × ZMod n) (hτ : ∀ v, τ (τ v) = -v)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ v : ZMod n × ZMod n, addOrderOf v = p ∧ ∀ k : ℕ, τ v ≠ k • v) :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n ∧ H.map τ = H}
      = nuTwo n := by p2m_exact_reverting @_root_.P2MW.S_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo.solution
