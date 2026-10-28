import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.T)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive Γ →+ R,
      ∀ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (hg : g⁻¹ * ModularGroup.T ^ Function.minimalPeriod (fun x => ModularGroup.T • x)
                (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ) * g ∈ Γ),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers ModularGroup.T) _)
              (g : Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ)) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_exists_addMonoidHom_conj_T_pow_minimalPeriod_eq_of_finsum_eq_zero.solution
