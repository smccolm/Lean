import Dubon2026.OriginalNormHomologySubgroupTransfer
import Dubon2026.OriginalFundamentalNormHomologyEquiv
import Dubon2026.OriginalFundamentalSubgroupSequence

/-! # The actual fundamental norm map on subgroup traces

The original fundamental and augmentation sequences themselves are
restricted to the subgroup. Their proved acyclicity supplies norm lifts;
no second choice of a fundamental extension is compared. This identifies
relative-trace images with genuine homology inclusion images, the finite
ground-norm input to DUB-17's prescribed-support fixed-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module

variable {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
  [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
  (h : ∀ T : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res T.subtype (originalFundamentalSplittingModule C φ)) 2))
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- The literal quotient trace of a subgroup-invariant internal Hom is
an actual full-group coefficient morphism. -/
def originalFundamentalSubgroupTraceMorphism
    (x : ((Rep.ihom M).obj C).quotientToInvariants S) : M ⟶ C :=
  Representation.linHom.invariantsEquivRepHom M C
    ⟨((((Rep.ihom M).obj C).quotientToInvariants S).ρ.norm x).val,
      originalSubgroup_trace_invariant S _ x⟩

/-- Under the actual norm-homology map, relative traces have exactly the
image of the actual subgroup homology map. Subgroup norm and acyclicity
premises are derived from the same original fundamental coefficient. -/
theorem originalFundamentalHomology_subgroup_trace_range :
    Set.range (fun x : ((Rep.ihom M).obj C).quotientToInvariants S =>
      originalFundamentalHomologyLinear M C φ p hG h
        (originalFundamentalSubgroupTraceMorphism M C S x)) =
      Set.range (groupHomology.map S.subtype
        (𝟙 (Rep.res S.subtype ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)))) 1) := by
  let B := originalFundamentalSplittingModule C φ
  let Y := (originalFundamentalSplittingShortComplex C φ).map (Rep.ihom M)
  let E := originalAugmentationInternalHomSequence M
  let YS := Y.map (Rep.resFunctor S.subtype)
  let ES := E.map (Rep.resFunctor S.subtype)
  letI : Module.Projective ℤ (Rep.res S.subtype M) := ‹Module.Projective ℤ M›
  have hYS : YS.ShortExact := originalInternalHom_shortExact (Rep.res S.subtype M)
    (originalFundamentalSubgroup_shortExact C φ S)
  have hES : ES.ShortExact := originalInternalHom_shortExact (Rep.res S.subtype M)
    (originalAugmentationSubgroup_shortExact (k := ℤ) S)
  have hE : E.ShortExact := originalAugmentationInternalHomSequence_shortExact M
  have hB (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 2) :=
    ⟨originalNestedSubgroup_zero B S T 1 (h _).1,
      originalNestedSubgroup_zero B S T 2 (h _).2⟩
  have hP (T : Subgroup S) :
      Limits.IsZero (groupCohomology
        (Rep.res T.subtype (Rep.res S.subtype (Rep.leftRegular ℤ G))) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res T.subtype (Rep.res S.subtype (Rep.leftRegular ℤ G))) 2) :=
    ⟨originalNestedSubgroup_zero _ S T 1 (originalRegularSubgroup_positive_zero _ 0),
      originalNestedSubgroup_zero _ S T 2 (originalRegularSubgroup_positive_zero _ 1)⟩
  have hBn := originalPGroup_internalHom_norm_preimages (Rep.res S.subtype M)
    (Rep.res S.subtype B) p (hG.to_subgroup S) hB
  have hBh := originalPGroup_internalHom_norm_homology (Rep.res S.subtype M)
    (Rep.res S.subtype B) p (hG.to_subgroup S) hB
  have hPh := originalPGroup_internalHom_norm_homology (Rep.res S.subtype M)
    (Rep.res S.subtype (Rep.leftRegular ℤ G)) p (hG.to_subgroup S) hP
  have htransfer (x : ((Rep.ihom M).obj C).quotientToInvariants S)
      (b : Y.X₂) (hb : (Rep.res S.subtype Y.X₂).ρ.norm b = Y.f.hom x.val)
      (y : groupHomology (Rep.res S.subtype E.X₃) 1)
      (hy : (groupHomology.H0Iso (Rep.res S.subtype Y.X₃)).hom
        (groupHomology.δ hES 1 0 rfl y) =
          Representation.Coinvariants.mk (Rep.res S.subtype Y.X₃).ρ (Y.g.hom b)) :
      originalFundamentalHomologyLinear M C φ p hG h
        (originalFundamentalSubgroupTraceMorphism M C S x) =
        groupHomology.map S.subtype (𝟙 _) 1 y := by
    have ht := originalSubgroup_norm_homology_transfer S (Y := Y)
      E.f E.g E.zero hE hES x b hb y hy
    apply originalFundamentalHomologyWitness_unique M C φ p hG h
      (originalFundamentalSubgroupTraceMorphism M C S x)
    · exact originalFundamentalHomologyLinear_witness M C φ p hG h _
    · exact ⟨b, ht.1, ht.2⟩
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨b, hb, y, hy, _⟩ := originalTwoSequence_norm_homology_witness hYS
      ES.f ES.g ES.zero hES hBn hBh.1 hPh.1 hPh.2 x.val x.property
    exact ⟨y, (htransfer x b hb y hy).symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hx, b, hb, hy⟩ := originalTwoSequence_homology_norm_lift hYS
      ES.f ES.g ES.zero hES y
    exact ⟨⟨x, hx⟩, htransfer ⟨x, hx⟩ b hb y hy⟩

end
end Dubon2026
