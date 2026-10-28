import Mathlib
import Definitions.Def_GaloisRep_Residual
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom

set_option autoImplicit false

open scoped MatrixGroups

theorem GaloisRep.exists_galoisRep_trace_eq_add_mul_of_unitsHom
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (κ : Type) [Field κ] [CharP κ p]
    (ψ₁ ψ₂ : (ZMod N)ˣ →* κˣ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            Matrix.trace (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) +
                  (ℓ : κ) * (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) ∧
            Matrix.det (ρ σ).val =
                (ψ₁ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) *
                  (ψ₂ (ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓN)) : κ) * (ℓ : κ)) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_galoisRep_trace_eq_add_mul_of_unitsHom.solution
