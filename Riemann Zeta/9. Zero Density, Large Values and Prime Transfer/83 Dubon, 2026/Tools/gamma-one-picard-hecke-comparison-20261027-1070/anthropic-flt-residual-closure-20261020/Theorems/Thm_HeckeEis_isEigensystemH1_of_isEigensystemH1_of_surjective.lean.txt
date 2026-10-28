import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective
    (N : ℕ) [NeZero N] {κ : Type} [Field κ] (h6 : (6 : κ) ≠ 0) (S₀ : Set ℕ)
    {V V'' : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] [AddCommGroup V''] [Module κ V'']
    (ρ : Representation κ (CongruenceSubgroup.Gamma0 N) V) (ρ'' : Representation κ (CongruenceSubgroup.Gamma0 N) V'')
    (a : ℕ → (V →ₗ[κ] V)) (a'' : ℕ → (V'' →ₗ[κ] V''))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (hcomm : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ∉ S₀ →
      a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (π : V →ₗ[κ] V'') (hπ : ∀ g : CongruenceSubgroup.Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
    (hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)
    (hsurj : Function.Surjective π)
    (lam : ℕ → κ) (h : HeckeEis.IsEigensystemH1 N ρ'' a'' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective.solution
