import Dubon2026.SourceOriginalPrimitiveGaloisRealization
import Dubon2026.SourcePadicIntegralRealizationConsumer

/-! DUB-17/18 -> modular residual association -> an actual stable
integral lattice in the prescribed primitive weight-two representation.
The finite original Tate module and its spanning specialization discharge
the lattice hypotheses. The actual original prime Hecke eigenvalues and
Galois action remain in the assembled conclusion. Residual reduction,
Frobenius/inertia and the full all-weight continuation chain remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimitive_stable_integral_lattice (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
    letI : ValuativeRel ℚ_[p] :=
      ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
        (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
        (L : Submodule 𝒪[E] (Fin 2 → E)),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
          π ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p] x) =
            (fun i => τ (sourcePrimitiveFieldCoefficient f ell.val) * π x i)) ∧
        (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
          (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x)) ∧
        Submodule.span E (L : Set (Fin 2 → E)) = ⊤ ∧
        Module.Free 𝒪[E] L ∧ Module.Finite 𝒪[E] L ∧ Module.finrank 𝒪[E] L = 2 ∧
        ∀ σ v, v ∈ L → (ρ σ).val *ᵥ v ∈ L := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
  letI : Module.Finite ℤ_[p] (TateModule p (originalJZero N)) :=
    (original_tate_free_finite_rank N p).2.1
  exact padic_realization_with_stable_lattice p E
    (fun ell : Nat.Primes => sourcePrimitiveFieldCoefficient f ell.val)
    (fun ell : Nat.Primes => TateModule.tateMap p (originalHeckePicard Qbar N ell.val))
    (originalTateGaloisRep N p) (originalPrimitive_continuous_galois_realization N p f).2

end
end Dubon2026.SourceFunctionField.OriginalChart
