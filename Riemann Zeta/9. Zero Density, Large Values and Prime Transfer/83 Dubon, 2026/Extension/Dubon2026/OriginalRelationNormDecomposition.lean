/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from the norm-decomposition step of P2M/Sol/
S_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective.lean
at revision 6e837e75355538c7f80bab5b956861e86c4eacc2. The original
relation presentation and pinned integral splitting shorten the proof.
-/
import Dubon2026.OriginalRelationHorseshoe
import Dubon2026.OriginalArbitraryRelationFree
import Dubon2026.OriginalCoefficientNormComposition

/-! # Decompose an actual relation norm through the coefficient sequence

For DUB-17's relation-extension dévissage, a zero obstruction supplies a
literal norm on the original relation lattice. A genuine horseshoe and
the pinned integral splitting extend its linear norm witness; projective
comparison then gives the required decomposition modulo the free cover.
Working directly with the original relation presentation avoids the two
extra presentation comparisons in the inspected external proof.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance 1100] Rep.hV2

/-- A literal norm on the original relation lattice decomposes through
the actual middle presentation modulo a morphism from the free cover. -/
theorem originalRelation_norm_decomposition
    {G : Type} [Group G] [Fintype G] (C : Rep.{0} ℤ G)
    {SB : ShortComplex (Rep.{0} ℤ G)} (hSB : SB.ShortExact)
    {R_I P_I : Rep.{0} ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂)
    (w_I : f_I ≫ g_I = 0)
    [Projective P_I]
    (ιR : originalRelationModule SB.X₁ ⟶ R_I)
    (ιP : Rep.free ℤ G SB.X₁ ⟶ P_I)
    (sq₁ : originalRelationInclusion SB.X₁ ≫ ιP = ιR ≫ f_I)
    (sq₂ : originalRelationFreeCover SB.X₁ ≫ SB.f = ιP ≫ g_I)
    (η : originalRelationModule SB.X₁ →ₗ[ℤ] C) :
    ∃ (ψ : R_I ⟶ C) (χ : Rep.free ℤ G SB.X₁ ⟶ C),
      originalCoefficientNormMorphism (originalRelationModule SB.X₁) C η =
        ιR ≫ ψ + originalRelationInclusion SB.X₁ ≫ χ := by
  obtain ⟨R, fR, gR, wR, hTR, j, q, wjq, hjq, s₁, s₂, _, _⟩ :=
    originalRelation_horseshoe hSB (originalRelationInclusion SB.X₁)
      (originalRelationFreeCover SB.X₁) (originalRelationShortComplex SB.X₁).zero
      (originalRelationShortComplex_shortExact SB.X₁)
      (originalRelationInclusion SB.X₃) (originalRelationFreeCover SB.X₃)
      (originalRelationShortComplex SB.X₃).zero (originalRelationShortComplex_shortExact SB.X₃)
  letI := originalArbitraryRelationModule_free SB.X₃
  letI : Module.Projective ℤ (ShortComplex.mk j q wjq).X₃ :=
    inferInstanceAs (Module.Projective ℤ (originalRelationModule SB.X₃))
  obtain ⟨r, hr⟩ := originalPresentation_integral_retraction (ShortComplex.mk j q wjq) hjq
  let ψt : R ⟶ C := originalCoefficientNormMorphism R C (η.comp r)
  have hjψ : j ≫ ψt = originalCoefficientNormMorphism (originalRelationModule SB.X₁) C η := by
    rw [originalCoefficientNorm_precomp]
    congr 1
    apply LinearMap.ext
    intro x
    exact congrArg η (hr x)
  obtain ⟨eR, eP, he₁, he₂⟩ := originalPresentation_exists_comparison
    (ShortComplex.mk f_I g_I w_I) (ShortComplex.mk fR gR wR) hTR (𝟙 SB.X₂)
  obtain ⟨t, ht⟩ := originalPresentation_comparison_difference
    (originalRelationShortComplex SB.X₁) (ShortComplex.mk fR gR wR) hTR SB.f
    (ιR ≫ eR) j (ιP ≫ eP) biprod.inl
    (by change originalRelationInclusion SB.X₁ ≫ (ιP ≫ eP) = (ιR ≫ eR) ≫ fR
        rw [← Category.assoc, sq₁, Category.assoc, he₁, Category.assoc])
    (by change originalRelationFreeCover SB.X₁ ≫ SB.f = (ιP ≫ eP) ≫ gR
        rw [sq₂, Category.assoc, ← he₂, Category.comp_id]) s₁ s₂
  refine ⟨eR ≫ ψt, -(t ≫ ψt), ?_⟩
  have hj : j = ιR ≫ eR - originalRelationInclusion SB.X₁ ≫ t := by
    change ιR ≫ eR - j = originalRelationInclusion SB.X₁ ≫ t at ht
    rw [← ht]
    abel
  rw [← hjψ, hj]
  ext x
  change ψt.hom (eR.hom (ιR.hom x) - t.hom ((originalRelationInclusion SB.X₁).hom x)) =
    ψt.hom (eR.hom (ιR.hom x)) + -(ψt.hom (t.hom ((originalRelationInclusion SB.X₁).hom x)))
  exact (map_sub ψt.hom _ _).trans (sub_eq_add_neg _ _)

end
end Dubon2026
