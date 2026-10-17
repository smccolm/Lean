import Dubon2026.OriginalTwoSequenceNormHomology
import Dubon2026.OriginalInternalHomNormHomology
import Dubon2026.OriginalInternalHomNormQuotient
import Dubon2026.OriginalLatticeIntegralDuality
import Dubon2026.OriginalFundamentalSplittingSequence

/-! # An original coefficient norm class represented by actual homology

The actual fundamental and augmentation sequences represent a
coefficient morphism modulo norms by first homology of the integral
dual. Every norm and homology condition is derived from the proved
subgroup acyclicity of the same fundamental coefficient. DUB-17 still
requires identification of its pairing with the induced H2 map.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (M C : Rep.{0} ℤ G)
variable [Module.Projective ℤ M]

/-- The literal original augmentation sequence after internal Hom from the integral lattice. -/
abbrev originalAugmentationInternalHomSequence : ShortComplex (Rep ℤ G) :=
  (originalAugmentationShortComplex ℤ G).map (Rep.ihom M)

/-- The literal internal-Hom augmentation sequence is short exact by projective lifting. -/
theorem originalAugmentationInternalHomSequence_shortExact :
    (originalAugmentationInternalHomSequence M).ShortExact :=
  originalInternalHom_shortExact M (originalAugmentationShortComplex_shortExact ℤ G)

variable [Fintype G]

/-- The actual middle norm lift and augmentation homology boundary for a coefficient morphism. This proposition alone supplies no witness or pairing comparison. -/
def OriginalFundamentalHomologyWitness (φ : groupCohomology.cocycles₂ C) (χ : M ⟶ C)
    (y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1) : Prop :=
  ∃ b : (Rep.ihom M).obj (originalFundamentalSplittingModule C φ),
    ((Rep.ihom M).obj (originalFundamentalSplittingModule C φ)).ρ.norm b =
      ((Rep.ihom M).map (originalFundamentalSplittingInclusion C φ)).hom χ.hom.toLinearMap ∧
    (groupHomology.H0Iso ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G))).hom
      (groupHomology.δ (originalAugmentationInternalHomSequence_shortExact M) 1 0 rfl y) =
        Representation.Coinvariants.mk ((Rep.ihom M).obj (originalAugmentationIdeal ℤ G)).ρ
          (((Rep.ihom M).map (originalFundamentalSplittingProjection C φ)).hom b)

/-- The same original fundamental coefficient constructs the actual homology witness, and the original morphism norm quotient vanishes exactly when that homology class is zero. -/
theorem originalFundamentalHomology_witness_exists
    (φ : groupCohomology.cocycles₂ C)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
    (χ : M ⟶ C) :
    ∃ y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1,
      OriginalFundamentalHomologyWitness M C φ χ y ∧
        ((Submodule.Quotient.mk χ : OriginalCoefficientNormQuotient M C) = 0 ↔ y = 0) := by
  let Y := (originalFundamentalSplittingShortComplex C φ).map (Rep.ihom M)
  let E := originalAugmentationInternalHomSequence M
  have hY : Y.ShortExact := originalInternalHom_shortExact M
    (originalFundamentalSplittingShortComplex_shortExact C φ)
  have hE : E.ShortExact := originalAugmentationInternalHomSequence_shortExact M
  have hB := originalPGroup_internalHom_norm_homology M
    (originalFundamentalSplittingModule C φ) p hG h
  have hP := originalPGroup_regularInternalHom_norm_homology M p hG
  obtain ⟨b, hb, y, hy, hc⟩ := originalTwoSequence_norm_homology_witness hY
    E.f E.g E.zero hE
    (originalPGroup_internalHom_norm_preimages M (originalFundamentalSplittingModule C φ) p hG h)
    hB.1 hP.1 hP.2 χ.hom.toLinearMap (originalMorphism_internalHom_invariant M C χ)
  refine ⟨y, ⟨b, hb, hy⟩, ?_⟩
  exact (originalCoefficientNormQuotient_zero_iff_internalHom_norm M C χ).trans hc

/-- For the original finite lattice, its actual integral pairing detects the constructed norm class; identification with the induced class-coefficient H2 map remains separate. -/
theorem originalFundamentalHomology_pairing_criterion [Module.Finite ℤ M]
    (φ : groupCohomology.cocycles₂ C)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))
    (χ : M ⟶ C) :
    ∃ y : groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ G ℤ)) 1,
      OriginalFundamentalHomologyWitness M C φ χ y ∧
        ((Submodule.Quotient.mk χ : OriginalCoefficientNormQuotient M C) = 0 ↔
          ∀ x : groupCohomology M 2, originalLatticeIntegralDuality M x y = 0) := by
  obtain ⟨y, hy, hc⟩ := originalFundamentalHomology_witness_exists M C φ p hG h χ
  refine ⟨y, hy, hc.trans ?_⟩
  constructor
  · intro hy0 x
    rw [hy0, map_zero]
  · exact originalLatticeIntegralDuality_right_nondegenerate M y

end
end Dubon2026
