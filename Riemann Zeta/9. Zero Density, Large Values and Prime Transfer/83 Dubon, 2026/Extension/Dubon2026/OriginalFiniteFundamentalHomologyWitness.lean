import Dubon2026.OriginalFiniteInternalHomNormHomology
import Dubon2026.OriginalFundamentalHomologyNormUniqueness

/-! # Actual fundamental homology witnesses without a p-group premise

The two original short exact sequences and their already proved norm
comparison now apply to an arbitrary finite group. These witnesses and
their uniqueness are the required input to DUB-17's finite relation
duality route. Identification with the actual H2 map remains separate.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
  [Module.Projective ℤ M] (φ : groupCohomology.cocycles₂ C)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology
      (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

include h

/-- The original finite-group fundamental coefficient constructs a
literal homology witness detecting zero of the actual norm class. -/
theorem originalFiniteFundamentalHomology_witness_exists (χ : M ⟶ C) :
    ∃ y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1,
      OriginalFundamentalHomologyWitness M C φ χ y ∧
        ((Submodule.Quotient.mk χ : OriginalCoefficientNormQuotient M C) = 0 ↔ y = 0) := by
  let Y := (originalFundamentalSplittingShortComplex C φ).map (Rep.ihom M)
  let E := originalAugmentationInternalHomSequence M
  have hY : Y.ShortExact := originalInternalHom_shortExact M
    (originalFundamentalSplittingShortComplex_shortExact C φ)
  have hE : E.ShortExact := originalAugmentationInternalHomSequence_shortExact M
  have hB := originalFinite_internalHom_norm_homology M
    (originalFundamentalSplittingModule C φ) h
  have hP := originalFinite_regularInternalHom_norm_homology M
  obtain ⟨b, hb, y, hy, hc⟩ := originalTwoSequence_norm_homology_witness hY
    E.f E.g E.zero hE
    (originalFinite_internalHom_norm_preimages M (originalFundamentalSplittingModule C φ) h)
    hB.1 hP.1 hP.2 χ.hom.toLinearMap (originalMorphism_internalHom_invariant M C χ)
  refine ⟨y, ⟨b, hb, hy⟩, ?_⟩
  exact (originalCoefficientNormQuotient_zero_iff_internalHom_norm M C χ).trans hc

/-- Every permitted literal middle norm lift gives the same actual
homology class, now for any finite group. -/
theorem originalFiniteFundamentalHomologyWitness_unique (χ : M ⟶ C)
    {y z : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1}
    (hy : OriginalFundamentalHomologyWitness M C φ χ y)
    (hz : OriginalFundamentalHomologyWitness M C φ χ z) : y = z := by
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨c, hc, hcz⟩ := hz
  let B := (Rep.ihom M).obj (originalFundamentalSplittingModule C φ)
  let I := (Rep.ihom M).obj (originalAugmentationIdeal ℤ G)
  let π : B ⟶ I := (Rep.ihom M).map (originalFundamentalSplittingProjection C φ)
  have hN : B.ρ.norm (b - c) = 0 := by rw [map_sub, hb, hc, sub_self]
  have hinj := (originalFinite_internalHom_norm_homology M
    (originalFundamentalSplittingModule C φ) h).1
  have hd := congrArg (Representation.Coinvariants.map B.ρ I.ρ π.hom) (hinj _ hN)
  rw [Representation.Coinvariants.map_mk, map_zero] at hd
  have he : Representation.Coinvariants.mk I.ρ (π.hom b) =
      Representation.Coinvariants.mk I.ρ (π.hom c) := by
    apply sub_eq_zero.mp
    simpa only [map_sub] using hd
  have hfirst := (originalFinite_regularInternalHom_norm_homology M).2
  have hm : Mono (groupHomology.δ
      (originalAugmentationInternalHomSequence_shortExact M) 1 0 rfl) :=
    groupHomology.mono_δ_of_isZero (originalAugmentationInternalHomSequence_shortExact M) 0 hfirst
  apply (ModuleCat.mono_iff_injective _).mp hm
  apply (groupHomology.H0Iso I).toLinearEquiv.injective
  exact hby.trans (he.trans hcz.symm)

end
end Dubon2026
