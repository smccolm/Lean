import Dubon2026.OriginalFundamentalNormQuotientInjectivity
import Dubon2026.OriginalRelationNormQuotient

/-! # The original relation obstruction and converse extension criterion

The actual relation kernel is already proved to be a finite integral
lattice. Apply the new converse norm theorem to that same kernel.
The existing coordinate extension construction then removes the norm
criterion premise; invariant norm divisibility remains an explicit
arithmetic obligation on DUB-17's finite class/Ext dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G]
variable (C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)
variable (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
variable (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
variable (h : ∀ S : Subgroup G,
  Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
include φ p hG ho h

/-- The original finite relation obstruction vanishes exactly when that same relation morphism has a literal coefficient norm preimage. -/
theorem originalFundamental_relation_obstruction_zero_iff_norm
    (B : Rep.{0} ℤ G) [Finite B] (χ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C χ = 0 ↔
      ∃ η : originalRelationModule B →ₗ[ℤ] C,
        originalCoefficientNormMorphism (originalRelationModule B) C η = χ := by
  letI := originalRelationModule_finite B
  letI := originalRelationModule_free B
  exact (originalRelationExtensionObstruction_zero_iff B C χ).trans
    (originalFundamental_h2_zero_iff_norm (originalRelationModule B) C φ p hG ho h χ)

/-- For a finite trivial prime-torsion coefficient, invariant norm divisibility is the remaining arithmetic premise needed to turn the actual zero obstruction into an extension through its original free cover. -/
theorem originalFundamental_relation_obstruction_zero_iff_extension
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
      (originalFundamental_relation_obstruction_zero_iff_norm C φ p hG ho h B χ).mp hz
    apply originalRelation_exists_extension_of_norm C p hnorm B hB htriv χ η.toAddMonoidHom
    intro x
    exact (congrArg (fun f : originalRelationModule B ⟶ C => f.hom x) hη).symm.trans
      (originalCoefficientNormMorphism_apply (originalRelationModule B) C η x)
  · rintro ⟨a, ha⟩
    exact originalRelationExtensionObstruction_zero_of_extension B C χ a ha

end
end Dubon2026
