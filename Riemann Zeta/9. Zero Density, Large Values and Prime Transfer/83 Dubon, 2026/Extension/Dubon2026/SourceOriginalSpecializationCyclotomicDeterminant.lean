import Dubon2026.SourceOriginalSpecializationPrimitiveImage
import Dubon2026.SourcePrimitiveOriginalTateGalois
import Dubon2026.SourceImageSpecializationDeterminant
import Dubon2026.SourceSpecializationBaseChangeIntertwiner

/-! DUB-17/18 -> the separate primitive determinant. The same original
spanning specialization and arithmetic representation inherit the actual
cyclotomic multiplier from the nondegenerate primitive Weil pairing.
All projector, image, pairing and invariance premises are derived. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct Matrix
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem original_specialization_cyclotomic_determinant_of_basis {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N p),
      π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x))
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (ρ σ).val.det = algebraMap ℚ_[p] E
      (algebraMap ℤ_[p] ℚ_[p] (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p])) := by
  refine (exists_original_primitive_specialization_image_equiv N p b P₀ lb f τ π hspan hH).elim
    fun s hs => hs.elim fun P h => ?_
  exact h.2.elim fun e he =>
    image_specialization_determinant (originalCoefficientWeilBilinear N p E)
      (π.liftBaseChange E) _ e he.1 (originalCoefficientWeilBilinear_self N p E) he.2.2.2
      ((originalRationalTateGaloisRep N p σ).baseChange E) (ρ σ).val
      (primitiveOriginalTateEvaluation_galois_commute N p b P₀ lb f τ σ s P)
      (liftBaseChange_intertwine π (originalRationalTateGaloisRep N p σ)
        (Matrix.toLin' (ρ σ).val) (fun x => (hact σ x).symm)) _
      (originalCoefficientWeilBilinear_cyclotomic N p E σ)

theorem original_specialization_cyclotomic_determinant
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) E)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N p),
      π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (hact : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : originalRationalTateModule N p),
      (ρ σ).val *ᵥ π x = π (originalRationalTateGaloisRep N p σ x))
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (ρ σ).val.det = algebraMap ℚ_[p] E
      (algebraMap ℤ_[p] ℚ_[p] (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p])) := by
  letI := finite_original_regularDifferentials N ℂ
  let b := Module.finBasis ℂ V
  obtain ⟨P₀⟩ := nonempty_original_places N ℂ
  exact original_specialization_cyclotomic_determinant_of_basis N p b P₀
    (originalPeriodLatticeBasis N b) f τ π ρ hspan hH hact σ

end
end Dubon2026.SourceFunctionField.OriginalChart
