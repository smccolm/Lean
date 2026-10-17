import Dubon2026.OriginalFiniteFundamentalConverseNorm
import Dubon2026.OriginalFundamentalRelationCriterion

/-! # The actual relation-extension criterion for any finite group

The enlarged arithmetic stage constructed for DUB-17 has no p-group
degree restriction. Use the proved finite-group converse norm criterion
and the existing literal coordinate extension. Full fundamental order,
subgroup vanishing, invariant norm roots and trivial prime-torsion action
remain explicit here; arithmetic assembly must discharge those inputs.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G]
variable (C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)
variable (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
variable (h : ∀ S : Subgroup G,
  Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
include φ ho h

/-- Without a p-group premise, zero of the actual relation obstruction
is equivalent to a literal coefficient norm preimage. -/
theorem originalFiniteFundamental_relation_obstruction_zero_iff_norm
    (B : Rep.{0} ℤ G) [Finite B] (χ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C χ = 0 ↔
      ∃ η : originalRelationModule B →ₗ[ℤ] C,
        originalCoefficientNormMorphism (originalRelationModule B) C η = χ := by
  letI := originalRelationModule_finite B
  letI := originalRelationModule_free B
  rw [originalRelationExtensionObstruction_zero_iff]
  constructor
  · exact originalFiniteFundamental_h2_zero_norm (originalRelationModule B) C φ ho h χ
  · rintro ⟨η, rfl⟩
    exact originalCoefficientNormMorphism_positive_map_zero (originalRelationModule B) C η 1

/-- Invariant norm roots give the genuine extension criterion for a
finite trivial prime-torsion coefficient over any finite group. -/
theorem originalFiniteFundamental_relation_obstruction_zero_iff_extension
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : G, C.ρ g d = d) ∧
      (∑ g : G, C.ρ g c) = p • d)
    (B : Rep.{0} ℤ G) [Finite B] (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : G) (b : B), B.ρ g b = b)
    (χ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C χ = 0 ↔
      ∃ a : Rep.free ℤ G B ⟶ C, originalRelationInclusion B ≫ a = χ := by
  constructor
  · intro hz
    obtain ⟨η, hη⟩ :=
      (originalFiniteFundamental_relation_obstruction_zero_iff_norm C φ ho h B χ).mp hz
    apply originalRelation_exists_extension_of_norm C p hnorm B hB htriv χ η.toAddMonoidHom
    intro x
    exact (congrArg (fun f : originalRelationModule B ⟶ C => f.hom x) hη).symm.trans
      (originalCoefficientNormMorphism_apply (originalRelationModule B) C η x)
  · rintro ⟨a, ha⟩
    exact originalRelationExtensionObstruction_zero_of_extension B C χ a ha

end
end Dubon2026
