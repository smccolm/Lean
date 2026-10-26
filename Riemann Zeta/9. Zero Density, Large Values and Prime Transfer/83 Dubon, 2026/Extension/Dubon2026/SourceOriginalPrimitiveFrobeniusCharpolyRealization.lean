import Dubon2026.SourceOriginalPrimitiveCyclotomicRealization
import Dubon2026.SourceCyclotomicFrobeniusCharpoly

/-! DUB-17/18 -> residual association. The same continuous unramified
primitive representation now has the exact arithmetic Frobenius determinant,
trace and characteristic polynomial, with its original Hecke specialization
and quadratic identity retained. Residue characteristic and roots of unity
evaluate the cyclotomic character; native Cayley-Hamilton determines trace. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Matrix
variable (N : ℕ) [NeZero N] (ell : ℕ) [Fact ell.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalPrimitive_continuous_unramified_frobenius_charpoly_realization
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
                τ (sourcePrimitiveFieldCoefficient f p) • (ρ σ).val ∧
              (ρ σ).val.det = (p : E) ∧
              (ρ σ).val.trace = τ (sourcePrimitiveFieldCoefficient f p) ∧
              (ρ σ).val.charpoly = Polynomial.X ^ 2 -
                Polynomial.C (τ (sourcePrimitiveFieldCoefficient f p)) * Polynomial.X +
                Polynomial.C (p : E) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  have hsrc := originalPrimitive_continuous_unramified_cyclotomic_realization N ell f
  rcases hsrc with ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr, hdet, hquad⟩
  refine ⟨hfin, τ, π, ρ, hρ, hspan, hhecke, hact, hunr, hdet, ?_⟩
  intro p hp hNp A hA σ hσ
  exact cyclotomic_frobenius_charpoly ell ρ hdet p hp
    (fun h => hNp (dvd_mul_of_dvd_right h N)) A hA σ hσ _
    (hquad p hp hNp A hA σ hσ)

end
end Dubon2026.SourceFunctionField.OriginalChart
