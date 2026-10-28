import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_perm_gamma0_cosetReps

theorem ModularCurve.exists_perm_gamma0_cosetReps (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : ∃ e : Equiv.Perm (Fin (ℓ + 1)), ∀ i : Fin (ℓ + 1), (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) * γ * (Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) (e i) : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma0 ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_perm_gamma0_cosetReps.solution
