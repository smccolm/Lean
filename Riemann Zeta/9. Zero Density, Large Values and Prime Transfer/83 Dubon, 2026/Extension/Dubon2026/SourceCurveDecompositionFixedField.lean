import Dubon2026.SourceCurveWildDifferentDecomposition

/-! Identify the fixed field used by the local wild different criterion
with the original decomposition fixed field. Native Galois correspondence
then shows that every automorphism over it fixes the actual upper place.
This is the necessary order-gap input for DUB-17/18 wild good reduction. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IntermediateField
variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable (v : Place K M)

theorem decomposition_fixedField_restrictScalars :
    (fixedField (v.toValuationSubring.decompositionSubgroup F)).restrictScalars K =
      fixedField (v.decompositionConstantAction (F := F)).range := by
  ext z
  change z ∈ fixedField (v.toValuationSubring.decompositionSubgroup F) ↔ _
  rw [mem_fixedField_iff, mem_fixedField_iff]
  constructor
  · intro h σ hσ
    obtain ⟨τ, rfl⟩ := hσ
    exact h τ τ.property
  · intro h σ hσ
    exact h (v.decompositionConstantAction ⟨σ, hσ⟩) ⟨⟨σ, hσ⟩, rfl⟩

variable [FiniteDimensional F M]

theorem decomposition_over_fixedField_eq_top :
    v.toValuationSubring.decompositionSubgroup
      (fixedField (v.toValuationSubring.decompositionSubgroup F)) = ⊤ := by
  letI : IsScalarTower K
      (fixedField (v.toValuationSubring.decompositionSubgroup F)) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply top_unique
  intro τ _
  obtain ⟨σ, rfl⟩ :=
    (subgroupEquivAlgEquiv (v.toValuationSubring.decompositionSubgroup F)).surjective τ
  rw [v.mem_decomposition_iff_comapEquiv_eq]
  change v.comapEquiv ((σ : M ≃ₐ[F] M).restrictScalars K) = v
  exact (v.mem_decomposition_iff_comapEquiv_eq (σ : M ≃ₐ[F] M)).mp σ.property

end
end Dubon2026.SourceCurve.Place
