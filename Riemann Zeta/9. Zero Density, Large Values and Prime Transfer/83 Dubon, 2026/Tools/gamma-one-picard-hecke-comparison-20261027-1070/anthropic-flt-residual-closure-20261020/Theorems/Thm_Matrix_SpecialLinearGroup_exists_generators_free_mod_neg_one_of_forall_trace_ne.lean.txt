import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.exists_generators_free_mod_neg_one_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1) :
    ∃ gens : Fin (1 + Γ.index / 6) → Γ,
      Subgroup.closure (Set.range gens ∪ {⟨-1, hneg⟩}) = ⊤ ∧
      ∀ (L : Type) [Group L] (v : Fin (1 + Γ.index / 6) → L),
        ∃ f : Γ →* L, ∀ i, f (gens i) = v i := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_generators_free_mod_neg_one_of_forall_trace_ne.solution
