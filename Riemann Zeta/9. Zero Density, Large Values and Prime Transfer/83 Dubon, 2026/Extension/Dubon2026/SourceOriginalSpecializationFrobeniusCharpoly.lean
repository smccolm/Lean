import Dubon2026.SourceOriginalSpecializationCyclotomicDeterminant
import Dubon2026.SourceCyclotomicFrobeniusCharpoly
import Dubon2026.SourceOriginalPrimitiveFrobeniusQuadraticRealization

/-! DUB-17/18 -> actual residual association. Apply the already proved
determinant and original Tate quadratic to any of the constructed original
spanning primitive specializations, including the existing integral and
residual realization. No second representation or lattice is required. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix Polynomial
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
variable {E : Type*} [Field E] [Algebra ℚ_[ell] E]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem original_specialization_frobenius_charpoly
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
      π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x))
    (A : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hNp : ¬p ∣ N * ell)
    (hA : (p : Qbar) ∈ A.nonunits) (σ : Qbar ≃ₐ[ℚ] Qbar)
    (hσ : ∃ hd : σ ∈ A.decompositionSubgroup ℚ,
      ∀ a : IsLocalRing.ResidueField A,
        (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) :
    (ρ σ).val.det = (p : E) ∧
    (ρ σ).val.trace = τ (sourcePrimitiveFieldCoefficient f p) ∧
    (ρ σ).val.charpoly = X ^ 2 - C (τ (sourcePrimitiveFieldCoefficient f p)) * X + C (p : E) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hq := original_specialization_quadratic N ell π ρ hspan hact p
    (τ (sourcePrimitiveFieldCoefficient f p)) (fun x => hH ⟨p, hp⟩ x) σ
    (GaussReduction.originalRationalTateGaloisRep_frobenius_quadratic_away
      A N p hp ell hNp hA σ hσ)
  exact (cyclotomic_frobenius_charpoly ell ρ
    (original_specialization_cyclotomic_determinant N ell f τ π ρ hspan hH hact)
    p hp (fun h => hNp (dvd_mul_of_dvd_right h N)) A hA σ hσ _ hq).2

end
end Dubon2026.SourceFunctionField.OriginalChart
