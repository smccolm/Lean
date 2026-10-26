import Dubon2026.SourceValuationCyclotomicFrobenius
import Dubon2026.SourceRankTwoQuadraticTrace

/-! DUB-17/18 -> actual residual association. Combine the cyclotomic
determinant and the independently established Frobenius quadratic at
the very same source valuation and automorphism. -/
namespace Dubon2026
noncomputable section
open Matrix Polynomial
local notation "Qbar" => AlgebraicClosure ℚ
variable (ell : ℕ) [Fact ell.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[ell] E]

theorem cyclotomic_frobenius_charpoly
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hdet : ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
      (ρ σ).val.det = algebraMap ℚ_[ell] E
        (algebraMap ℤ_[ell] ℚ_[ell]
          (cyclotomicCharacter Qbar ell σ.toRingEquiv : ℤ_[ell])))
    (p : ℕ) (hp : p.Prime) (hpl : ¬p ∣ ell)
    (A : ValuationSubring Qbar) (hA : (p : Qbar) ∈ A.nonunits)
    (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hσ : ∃ hd : σ ∈ A.decompositionSubgroup ℚ,
      ∀ a : IsLocalRing.ResidueField A,
        (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p)
    (a : E) (hq : (ρ σ).val * (ρ σ).val + p • 1 = a • (ρ σ).val) :
    (ρ σ).val * (ρ σ).val + p • 1 = a • (ρ σ).val ∧
    (ρ σ).val.det = (p : E) ∧ (ρ σ).val.trace = a ∧
    (ρ σ).val.charpoly = X ^ 2 - C a * X + C (p : E) := by
  have hd : (ρ σ).val.det = (p : E) := by
    rw [hdet σ, valuation_cyclotomic_frobenius A p hp ell hpl hA σ hσ]
    simp only [map_natCast]
  have hq' : (ρ σ).val * (ρ σ).val + (p : E) • 1 = a • (ρ σ).val := by
    simpa only [Nat.cast_smul_eq_nsmul] using hq
  exact ⟨hq, hd, rank_two_trace_of_determinant_quadratic (ρ σ) a _ hd hq',
    rank_two_charpoly_of_determinant_quadratic (ρ σ) a _ hd hq'⟩

end
end Dubon2026
