import Dubon2026.OriginalFundamentalGroupChangeSequence
import Dubon2026.OriginalNormHomologySubgroupDiagram
import Dubon2026.OriginalFundamentalSubgroupNormHomology

/-! # The actual fundamental norm-homology map under subgroup change

Compatibility of the genuine H2 classes constructs the coefficient
diagram and carries actual fundamental norm witnesses to their relative
traces. Uniqueness identifies the resulting homology map. This is the
local/global comparison needed for DUB-17's outside-unit inertia image.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G]
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]
  (C : Rep.{0} ℤ S) (D : Rep.{0} ℤ G) (ℓ : C ⟶ Rep.res S.subtype D)
  (φ : groupCohomology.cocycles₂ C) (ψ : groupCohomology.cocycles₂ D)
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (hC : ∀ T : Subgroup S,
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 2))
  (hD : ∀ T : Subgroup G,
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule D ψ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res T.subtype (originalFundamentalSplittingModule D ψ)) 2))

/-- The actual norm-homology map of a compatible coefficient morphism
commutes with subgroup inclusion and the literal relative trace. -/
theorem originalFundamentalHomology_groupChange
    (hclass : groupCohomology.map (MonoidHom.id S) ℓ 2 (groupCohomology.H2π C φ) =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype D)) 2 (groupCohomology.H2π D ψ))
    (χ : Rep.trivial ℤ S ℤ ⟶ C) :
    let x : ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj D).quotientToInvariants S :=
      ⟨(χ ≫ ℓ).hom.toLinearMap,
        originalMorphism_internalHom_invariant (Rep.trivial ℤ S ℤ) (Rep.res S.subtype D) (χ ≫ ℓ)⟩
    originalFundamentalHomologyLinear (Rep.trivial ℤ G ℤ) D ψ p hG hD
      (originalFundamentalSubgroupTraceMorphism (Rep.trivial ℤ G ℤ) D S x) =
      groupHomology.map S.subtype (𝟙 _) 1
        (originalFundamentalHomologyLinear (Rep.trivial ℤ S ℤ) C φ p (hG.to_subgroup S) hC χ) := by
  dsimp only
  let MS := Rep.trivial ℤ S ℤ
  let MG := Rep.trivial ℤ G ℤ
  let X := (originalFundamentalSplittingShortComplex C φ).map (Rep.ihom MS)
  let Y := (originalFundamentalSplittingShortComplex D ψ).map (Rep.ihom MG)
  let E := originalAugmentationInternalHomSequence MS
  let F := originalAugmentationInternalHomSequence MG
  obtain ⟨m, hm₁, hm₃⟩ := originalFundamentalGroupChangeSequenceMap_exists C D S.subtype ℓ φ ψ hclass
  let mi : X ⟶ Y.map (Rep.resFunctor S.subtype) := (Rep.ihom MS).mapShortComplex.map m
  let ni : E ⟶ F.map (Rep.resFunctor S.subtype) :=
    (Rep.ihom MS).mapShortComplex.map (originalAugmentationGroupChangeSequenceMap S.subtype)
  have hni : ni.τ₁ = mi.τ₃ := congrArg (Rep.ihom MS).map hm₃.symm
  let y := originalFundamentalHomologyLinear MS C φ p (hG.to_subgroup S) hC χ
  obtain ⟨b, hb, hy⟩ := originalFundamentalHomologyLinear_witness MS C φ p (hG.to_subgroup S) hC χ
  let x : X.X₁.ρ.invariants :=
    ⟨χ.hom.toLinearMap, originalMorphism_internalHom_invariant MS C χ⟩
  have ht := originalNormHomology_subgroup_diagram S (X := X) (Y := Y) mi
    E.f E.g E.zero (originalAugmentationInternalHomSequence_shortExact MS)
    F.f F.g F.zero (originalAugmentationInternalHomSequence_shortExact MG)
    ni hni x b hb y hy
  have hx : ((Rep.invariantsFunctor ℤ S).map mi.τ₁ x).val = (χ ≫ ℓ).hom.toLinearMap := by
    change ((Rep.ihom MS).map m.τ₁).hom χ.hom.toLinearMap = _
    rw [hm₁]
    rfl
  apply originalFundamentalHomologyWitness_unique MG D ψ p hG hD
  · exact originalFundamentalHomologyLinear_witness MG D ψ p hG hD _
  · refine ⟨mi.τ₂.hom b, ?_, ?_⟩
    · have hx' : (Rep.invariantsFunctor ℤ S).map mi.τ₁ x =
          (⟨(χ ≫ ℓ).hom.toLinearMap,
            originalMorphism_internalHom_invariant MS (Rep.res S.subtype D) (χ ≫ ℓ)⟩ :
              ((Rep.ihom MG).obj D).quotientToInvariants S) := Subtype.ext hx
      rw [hx'] at ht
      exact ht.1
    · exact ht.2

end
end Dubon2026
