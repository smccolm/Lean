import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_Subgroup_exists_eq_mul_of_index_inf_eq

theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G] (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) : ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_exists_eq_mul_of_index_inf_eq.solution
