import Dubon2026.OriginalFundamentalHomologyWitness

/-! # Linearity of the actual norm-lift homology relation

The original witnesses are closed under addition and integral scaling.
This is needed to identify the actual norm quotient with homology for
the norm-index input to DUB-17's prescribed-support norm field.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
  [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)

/-- Adding literal middle lifts adds the original morphisms and their actual homology witnesses. -/
theorem originalFundamentalHomologyWitness_add
    {χ ψ : M ⟶ C}
    {y z : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1}
    (hy : OriginalFundamentalHomologyWitness M C φ χ y)
    (hz : OriginalFundamentalHomologyWitness M C φ ψ z) :
    OriginalFundamentalHomologyWitness M C φ (χ + ψ) (y + z) := by
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨c, hc, hcz⟩ := hz
  refine ⟨b + c, ?_, ?_⟩
  · change _ = ((Rep.ihom M).map (originalFundamentalSplittingInclusion C φ)).hom
      (χ.hom.toLinearMap + ψ.hom.toLinearMap)
    rw [map_add, hb, hc]
    exact ((Rep.ihom M).map (originalFundamentalSplittingInclusion C φ)).hom.toLinearMap.map_add
      χ.hom.toLinearMap ψ.hom.toLinearMap |>.symm
  · let F := (groupHomology.H0Iso ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G))).hom.hom.comp
      (groupHomology.δ (originalAugmentationInternalHomSequence_shortExact M) 1 0 rfl).hom
    let B := (Representation.Coinvariants.mk ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G)).ρ).comp
      ((Rep.ihom M).map (originalFundamentalSplittingProjection C φ)).hom.toLinearMap
    exact (F.map_add y z).trans ((congrArg₂ (· + ·) hby hcz).trans (B.map_add b c).symm)

/-- Scaling a literal middle lift scales its original morphism and actual homology witness. -/
theorem originalFundamentalHomologyWitness_smul
    {χ : M ⟶ C}
    {y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1}
    (hy : OriginalFundamentalHomologyWitness M C φ χ y) (n : ℤ) :
    OriginalFundamentalHomologyWitness M C φ (n • χ) (n • y) := by
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨n • b, ?_, ?_⟩
  · change _ = ((Rep.ihom M).map (originalFundamentalSplittingInclusion C φ)).hom
      (n • χ.hom.toLinearMap)
    exact (map_zsmul ((Rep.ihom M).obj (originalFundamentalSplittingModule C φ)).ρ.norm n b).trans
      ((congrArg (n • ·) hb).trans
        (map_zsmul ((Rep.ihom M).map (originalFundamentalSplittingInclusion C φ)).hom.toLinearMap
          n χ.hom.toLinearMap).symm)
  · let F := (groupHomology.H0Iso ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G))).hom.hom.comp
      (groupHomology.δ (originalAugmentationInternalHomSequence_shortExact M) 1 0 rfl).hom
    let B := (Representation.Coinvariants.mk ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G)).ρ).comp
      ((Rep.ihom M).map (originalFundamentalSplittingProjection C φ)).hom.toLinearMap
    exact (map_zsmul F n y).trans ((congrArg (n • ·) hby).trans (map_zsmul B n b).symm)

end
end Dubon2026
