import Dubon2026.SourceOriginalPrimitiveIntegralLattice
import Dubon2026.SourcePadicResidualLocalConsumer

/-! DUB-17/18 -> modular residual association -> actual primitive
weight-two residual realization. The original integral Tate module
constructs a stable lattice and a basis. Its genuine integral matrices
reduce entrywise to a continuous representation over the actual finite
characteristic-p residue field. All original prime Fourier eigenvalues,
rational Tate spanning and arithmetic intertwining remain explicit.
Frobenius/inertia compatibility and all-weight continuation are still
required; this realization alone does not assert residual association. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open scoped ValuativeRel
open Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimitive_continuous_residual_realization (f : PrimitiveCuspForm N 2) :
    letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
    let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
    letI : ValuativeRel ℚ_[p] :=
      ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))
    ∃ (_ : UniformSpace E) (_ : ValuativeRel E),
      letI : TopologicalSpace 𝓀[E] :=
        inferInstanceAs (TopologicalSpace (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]))
      IsUniformAddGroup E ∧ IsNonarchimedeanLocalField E ∧ IsModuleTopology ℚ_[p] E ∧
      (ValuativeRel.valuation ℚ_[p]).HasExtension (ValuativeRel.valuation E) ∧
      Finite 𝓀[E] ∧ DiscreteTopology 𝓀[E] ∧ CharP 𝓀[E] p ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
        (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
        (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
        (e : (Fin 2 → E) ≃ₗ[E] (Fin 2 → E))
        (ρint : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝒪[E])
        (ρres : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) 𝓀[E]),
        Continuous ρ ∧ Submodule.span E (Set.range π) = ⊤ ∧
        (∀ (ell : Nat.Primes) (x : originalRationalTateModule N p),
          π ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p] x) =
            (fun i => τ (sourcePrimitiveFieldCoefficient f ell.val) * π x i)) ∧
        (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
          (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x)) ∧
        Continuous ρint ∧ Continuous ρres ∧
        (∀ σ i j, (ρres σ).val i j = IsLocalRing.residue 𝒪[E] ((ρint σ).val i j)) ∧
        ∀ σ v, (ρint σ).val.map (algebraMap 𝒪[E] E) *ᵥ e v = e ((ρ σ).val *ᵥ v) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  let E := commonCoefficientField (sourcePrimitiveCoefficientField f) ℚ_[p]
  exact padic_source_local_integral_residual_realization p E
    (fun ell : Nat.Primes => sourcePrimitiveFieldCoefficient f ell.val)
    (fun ell : Nat.Primes =>
      (TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p])
    (originalRationalTateGaloisRep N p) (originalPrimitive_stable_integral_lattice N p f)

end
end Dubon2026.SourceFunctionField.OriginalChart
