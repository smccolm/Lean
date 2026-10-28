import Mathlib
import P2M.Util
import P2M.Sol.S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom

set_option autoImplicit false

open scoped TensorProduct

theorem Module.exists_ne_zero_forall_baseChange_eq_smul_of_algHom
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {F : Type*} [Field F] [Algebra R F]
    {ι : Type*} (t : ι → Module.End R M) (ht : ∀ i j, Commute (t i) (t j))
    (χ : ↥(Algebra.adjoin R (Set.range t)) →ₐ[R] F) :
    ∃ y : F ⊗[R] M, y ≠ 0 ∧
      ∀ i, (t i).baseChange F y = χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ • y := by p2m_exact_reverting @_root_.P2MW.S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom.solution
