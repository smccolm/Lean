import Dubon2026.OriginalInducedRelationExtension

/-! # Actual quotient-class extension through the induced free cover

The original normalized arithmetic quotient system derives the class
data used by DUB-17's induced middle-extension criterion. The remaining
norm-root and trivial-kernel-action premises match the already constructed
arithmetic tower; their final common-stage assembly is still required.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- The actual arithmetic quotient has the induced extension criterion,
with all class-system and comparison inputs derived from its original
normalized quotient system. -/
theorem originalClassQuotient_induced_relation_extension
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime] (N : Subgroup Gal(L/K)) [Fintype N]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : N, (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (ψ : Rep.ind N.subtype (originalRelationModule (Rep.res N.subtype B)) ⟶
      originalIdeleClassesModOutsideRep K L S hS) :
    groupCohomology.δ (originalInducedRelationSequence_shortExact N B) 1 2 rfl ≫
        (groupCohomology.functor ℤ Gal(L/K) 2).map ψ = 0 ↔
      ∃ χ : Rep.ind N.subtype (Rep.free ℤ N (Rep.res N.subtype B)) ⟶
        originalIdeleClassesModOutsideRep K L S hS,
        (Rep.indFunctor ℤ N.subtype).map (originalRelationInclusion (Rep.res N.subtype B)) ≫ χ = ψ := by
  obtain ⟨u, hu, h1, hc, hg, _⟩ := hsys
  exact originalInducedRelation_obstruction_zero_iff_extension _ u
    (hu.trans (IsGalois.card_aut_eq_finrank K L).symm) h1 hc hg p N hnorm B hB hNB ψ

end
end Dubon2026
