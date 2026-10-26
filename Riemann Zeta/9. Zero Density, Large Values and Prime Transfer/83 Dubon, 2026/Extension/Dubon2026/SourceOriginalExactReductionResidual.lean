import Dubon2026.SourceOriginalPrescribedReductionResidual

/-! DUB-17/18 -> prescribed residual association. Instantiate the completed
number-field construction with the exact original Fourier field and its
identity embedding. No coefficient field, place, local structure, lattice
or residual compatibility assumption is supplied. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open Matrix Polynomial
open scoped NumberField
local notation "Qbar" => AlgebraicClosure ℚ
variable (N ell : ℕ) [NeZero N] (hell : ell.Prime) [Fact ell.Prime]
variable (K : Type) [Field K] [TopologicalSpace K] [CharP K ell]
variable (f : PrimitiveCuspForm N 2)
variable (φ : 𝓞 (sourcePrimitiveCoefficientField f) →+* K)

include hell in
theorem originalPrimitive_prescribed_reduction_residual_realization :
    ∃ ρ : (Qbar ≃ₐ[ℚ] Qbar) →* GeneralLinearGroup (Fin 2) K,
      Continuous ρ ∧ (Set.range ρ).Finite ∧
      (∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            σ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype →
              ρ σ = 1) ∧
      ∀ q : ℕ, q.Prime → ¬q ∣ N * ell →
        ∀ A : ValuationSubring Qbar, (q : Qbar) ∈ A.nonunits →
          ∀ σ : Qbar ≃ₐ[ℚ] Qbar,
            (∃ hd : σ ∈ A.decompositionSubgroup ℚ,
              ∀ z : IsLocalRing.ResidueField A,
                (⟨σ, hd⟩ : A.decompositionSubgroup ℚ) • z = z ^ q) →
            let a : 𝓞 (sourcePrimitiveCoefficientField f) := ⟨sourcePrimitiveFieldCoefficient f q,
              sourcePrimitiveFieldCoefficient_isIntegral f (by norm_num) q⟩
            (ρ σ).val.charpoly = X ^ 2 - C (φ a) * X + C (q : K) ∧
              (ρ σ).val.trace = φ a ∧ (ρ σ).val.det = (q : K) := by
  letI := sourcePrimitiveCoefficientField_numberField f (by norm_num)
  exact originalPrimitive_numberField_reduction_residual_realization N ell hell K
    (sourcePrimitiveCoefficientField f) f (AlgHom.id ℚ _) φ

end
end Dubon2026.SourceFunctionField.OriginalChart
