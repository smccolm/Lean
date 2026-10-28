import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree

open ModularCurve
theorem AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (σ : A →+ A) (hσ : ∀ a : A, σ (σ a) + σ a + a = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = nuThree n := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_add_self_add_id_eq_zero_eq_nuThree.solution
