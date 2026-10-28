import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import P2M.Util
import P2M.Sol.S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_or_of_isEigensystemH1_of_injective
    (N : ℕ) {K : Type} [Field K] (S₀ : Set ℕ)
    {V' V : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
    (ρ' : Representation K (CongruenceSubgroup.Gamma0 N) V') (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a' : ℕ → (V' →ₗ[K] V')) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (ι : V' →ₗ[K] V) (hι : ∀ g : CongruenceSubgroup.Gamma0 N, ι ∘ₗ ρ' g = ρ g ∘ₗ ι)
    (hιa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ι ∘ₗ a' ℓ = a ℓ ∘ₗ ι) (hinj : Function.Injective ι)
    (q₀ : V) (hq₀ : ∀ v : V, (∀ g : CongruenceSubgroup.Gamma0 N, ρ g v - v ∈ LinearMap.range ι) →
      ∃ r : K, v - r • q₀ ∈ LinearMap.range ι)
    (c : ℕ → K) (hc : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a ℓ q₀ - c ℓ • q₀ ∈ LinearMap.range ι)
    (lam : ℕ → K) (h : HeckeEis.IsEigensystemH1 N ρ' a' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam ∨
      ((∀ g : CongruenceSubgroup.Gamma0 N, ρ g q₀ - q₀ ∈ LinearMap.range ι) ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = ((ℓ : K) + 1) * c ℓ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective.solution
