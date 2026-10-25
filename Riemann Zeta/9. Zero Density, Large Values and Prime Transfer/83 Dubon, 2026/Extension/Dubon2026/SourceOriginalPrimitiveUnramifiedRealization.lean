import Dubon2026.SourceOriginalSpecializationInertia

/-! DUB-17/18 -> original primitive weight-two Galois association.
The actual continuous primitive-form realization is unramified away from
the level and Tate prime. Its original coefficient embedding, spanning
specialization, literal Fourier eigenvalues and arithmetic action are all
retained. The inertia identity is derived for this same representation.
Frobenius traces, residual association and all-weight continuation remain
separate required conclusions. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_continuous_unramified_galois_realization (f : PrimitiveCuspForm N 2) :
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
        ∀ (p : ℕ), p.Prime → ¬p ∣ N * ell →
          ∀ A : ValuationSubring Qbar, (p : Qbar) ∈ A.nonunits →
            ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
              σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype → ρ σ = 1 := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  obtain ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact⟩ :=
    originalPrimitive_continuous_galois_realization N ell f
  refine ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, ?_⟩
  intro p hp hNp A hA σ hσ
  exact original_specialization_inertia_identity N ell π ρ hspan hact A p hp hNp hA σ hσ

end
end Dubon2026.SourceFunctionField.OriginalChart
