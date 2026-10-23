import Dubon2026.SourceOriginalPrimitiveTateSpecialization

/-! DUB-17/18 -> modular residual association -> continuous primitive
weight-two Galois realization from the original Jacobian. Construct the
regular and lattice bases and the auxiliary place from their proved
existence. The actual finite coefficient field, literal prime eigenvalues,
spanning specialization and original arithmetic action are retained.
This does not yet assert Frobenius traces or residual association, and
does not replace the all-weight source contract. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimitive_continuous_galois_realization (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
    letI : TopologicalSpace E := moduleTopology ℚ_[p] E
    FiniteDimensional ℚ_[p] E ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
        (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
          π ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p] x) =
            (fun i => τ (sourcePrimitiveFieldCoefficient f ell.val) * π x i)) ∧
        ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
          (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  refine ⟨inferInstance, ?_⟩
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  exact originalPrimitiveTate_specialization_of_basis N p b P₀ (originalPeriodLatticeBasis N b) f

end
end Dubon2026.SourceFunctionField.OriginalChart
