import Dubon2026.SourceOriginalTateFrobeniusQuadratic
import Dubon2026.SourceOriginalSpecializationQuadratic
import Dubon2026.SourceOriginalPrimitiveUnramifiedRealization

/-! DUB-17/18 -> actual primitive weight-two residual association.
Retain the same constructed continuous unramified rank-two realization and
derive its Frobenius quadratic identity from the actual original Tate
identity. The existing coefficient embedding, spanning specialization,
prime Fourier eigenvalues and original arithmetic action are preserved.
The separate determinant and residual-association obligations remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_continuous_unramified_frobenius_quadratic_realization
    (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[ell]
    letI : TopologicalSpace E := moduleTopology ℚ_[ell] E
    FiniteDimensional ℚ_[ell] E ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
        (π : originalRationalTateModule N ell →ₗ[ℚ_[ell]] (Fin 2 → E))
        (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ (q : Nat.Primes) (x : originalRationalTateModule N ell),
          π ((TateModule.tateMap ell (originalHeckePicard Qbar N q.val)).baseChange ℚ_[ell] x) =
            (fun i => τ (sourcePrimitiveFieldCoefficient f q.val) * π x i)) ∧
        (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N ell),
          (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N ell σ x)) ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ N * ell →
          ∀ A : ValuationSubring Qbar, (p : Qbar) ∈ A.nonunits →
            ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
              σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype → ρ σ = 1) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ell →
          ∀ A : ValuationSubring Qbar, (p : Qbar) ∈ A.nonunits →
            ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
              (∃ hd : σ ∈ A.decompositionSubgroup ℚ,
                ∀ a : IsLocalRing.ResidueField A,
                  (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) →
              (ρ σ).val * (ρ σ).val + p • 1 =
                τ (sourcePrimitiveFieldCoefficient f p) • (ρ σ).val := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  obtain ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr⟩ :=
    originalPrimitive_continuous_unramified_galois_realization N ell f
  refine ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr, ?_⟩
  intro p hp hNp A hA σ hσ
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply original_specialization_quadratic N ell π ρ hspan hact p
    (τ (sourcePrimitiveFieldCoefficient f p))
  · intro x
    exact hhecke ⟨p, hp⟩ x
  · exact GaussReduction.originalRationalTateGaloisRep_frobenius_quadratic_away
      A N p hp ell hNp hA σ hσ

end
end Dubon2026.SourceFunctionField.OriginalChart
