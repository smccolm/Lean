import Mathlib
import P2M.Util
import P2M.Sol.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le

theorem LinearEquiv.exists_forall_finrank_inf_map_pow_add_finrank_inf_le
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
    (φ : W ≃ₗ[k] W) (P B P' B' : Submodule k W) (hPB : P ≤ B) (hP'B' : P' ≤ B')
    (hP : P.map (φ : W →ₗ[k] W) ≤ P) (hB : B.map (φ : W →ₗ[k] W) ≤ B)
    (hP' : P'.map (φ.symm : W →ₗ[k] W) ≤ P') (hB' : B'.map (φ.symm : W →ₗ[k] W) ≤ B')
    (hfin : ∀ M : ℕ, FiniteDimensional k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)))
    (hgen : ∃ M₁ : ℕ, B ≤ ⨆ j : ℕ,
      (B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M₁)).map ((φ : W →ₗ[k] W) ^ j))
    (hgen' : ∃ M₁ : ℕ, B' ≤ ⨆ j : ℕ,
      (B' ⊓ B.map ((φ.symm : W →ₗ[k] W) ^ M₁)).map ((φ.symm : W →ₗ[k] W) ^ j))
    (htor : ∀ y ∈ B, ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ : W →ₗ[k] W) c y ∈ P)
    (htor' : ∀ y ∈ B', ∃ c : Polynomial k, c.Monic ∧
      Polynomial.aeval (φ.symm : W →ₗ[k] W) c y ∈ P') :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Module.finrank k ↥(P ⊓ P'.map ((φ : W →ₗ[k] W) ^ M)) + Module.finrank k ↥(B ⊓ B') ≤
        Module.finrank k ↥(B ⊓ B'.map ((φ : W →ₗ[k] W) ^ M)) +
          Module.finrank k ↥(P ⊓ P') := by p2m_exact_reverting @_root_.P2MW.S_LinearEquiv_exists_forall_finrank_inf_map_pow_add_finrank_inf_le.solution
