import Dubon2026.SourceOriginalPrimitiveFrobeniusQuadraticRealization
import Dubon2026.SourceOriginalSpecializationCyclotomicDeterminant

/-! DUB-17/18 -> primitive determinant and residual association. Retain the
same constructed continuous unramified original Tate specialization, every
prime Fourier eigenvalue and the actual Frobenius quadratic identity, and
derive its determinant as the original cyclotomic multiplier. No pairing,
projector, image, determinant or comparison assumption is supplied. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_continuous_unramified_cyclotomic_realization
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
        (∀ σ : Qbar ≃ₐ[ℚ] Qbar,
          (ρ σ).val.det = algebraMap ℚ_[ell] E
            (algebraMap ℤ_[ell] ℚ_[ell]
              (cyclotomicCharacter Qbar ell σ.toRingEquiv : ℤ_[ell]))) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ell →
          ∀ A : ValuationSubring Qbar, (p : Qbar) ∈ A.nonunits →
            ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
              (∃ hd : σ ∈ A.decompositionSubgroup ℚ,
                ∀ a : IsLocalRing.ResidueField A,
                  (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) →
              (ρ σ).val * (ρ σ).val + p • 1 =
                τ (sourcePrimitiveFieldCoefficient f p) • (ρ σ).val := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  obtain ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr, hquad⟩ :=
    originalPrimitive_continuous_unramified_frobenius_quadratic_realization N ell f
  refine ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr, ?_, hquad⟩
  intro σ
  exact original_specialization_cyclotomic_determinant N ell f τ.toRingHom π ρ hspan
    (fun q x => hhecke q x) hact σ

end
end Dubon2026.SourceFunctionField.OriginalChart
