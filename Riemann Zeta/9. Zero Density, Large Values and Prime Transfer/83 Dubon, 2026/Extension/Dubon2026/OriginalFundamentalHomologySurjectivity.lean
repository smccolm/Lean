import Dubon2026.OriginalTwoSequenceHomologyNormLift
import Dubon2026.OriginalFundamentalHomologyWitness

/-! # Surjectivity of the original norm-class homology representation

Every actual first homology class of the integral dual comes from an
original coefficient morphism and a literal middle norm lift. This
reverse construction is needed for the abelian norm index used in
the norm-field step of DUB-17's invariant norm divisibility chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Every actual dual homology class has an original coefficient morphism and the required literal fundamental norm lift. -/
theorem originalFundamentalHomology_witness_surjective
    {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
    (y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1) :
    ∃ χ : M ⟶ C, OriginalFundamentalHomologyWitness M C φ χ y := by
  let Y := (originalFundamentalSplittingShortComplex C φ).map (Rep.ihom M)
  let E := originalAugmentationInternalHomSequence M
  have hY : Y.ShortExact := originalInternalHom_shortExact M
    (originalFundamentalSplittingShortComplex_shortExact C φ)
  have hE : E.ShortExact := originalAugmentationInternalHomSequence_shortExact M
  obtain ⟨x, hx, b, hb, hy⟩ := originalTwoSequence_homology_norm_lift hY
    E.f E.g E.zero hE y
  let χ := Representation.linHom.invariantsEquivRepHom M C ⟨x, hx⟩
  exact ⟨χ, b, hb, hy⟩

end
end Dubon2026
