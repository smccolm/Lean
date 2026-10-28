import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
    (p : ℕ) [Fact p.Prime] (N : ℕ) {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V) (a : ℕ → (V →ₗ[K] V))
    (μ : V →ₗ[K] K) (c : ℕ → K)
    (hμρ : ∀ δ : CongruenceSubgroup.Gamma0 N, (p : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → μ ∘ₗ ρ δ = μ)
    (hμa : ∀ ℓ : ℕ, μ ∘ₗ a ℓ = c ℓ • μ)
    (z : CongruenceSubgroup.Gamma0 N → V) (hz : z ∈ HeckeEis.coeffCocycles ρ) :
    ∃ y : Additive ↥(CongruenceSubgroup.Gamma0 (N * p)) →+ K,
      (∀ (γ : CongruenceSubgroup.Gamma0 (N * p)) (δ : CongruenceSubgroup.Gamma0 N),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * HeckeEis.alphaMat p
            = HeckeEis.alphaMat p * ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) →
        y (Additive.ofMul γ) = μ (z δ)) ∧
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ≠ p →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
          a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ) →
        ∀ (lam : K) (T : HeckeEis.coeffH1 ρ →ₗ[K] HeckeEis.coeffH1 ρ),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T) →
        T (HeckeEis.coeffH1Mk ρ ⟨z, hz⟩) = lam • HeckeEis.coeffH1Mk ρ ⟨z, hz⟩ →
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
         c ℓ • HeckeEis.heckeOperatorHom (N * p) ℓ K y = lam • y) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq.solution
