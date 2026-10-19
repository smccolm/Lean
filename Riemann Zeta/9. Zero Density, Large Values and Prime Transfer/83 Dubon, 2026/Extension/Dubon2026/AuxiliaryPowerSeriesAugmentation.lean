import Dubon2026.AuxiliaryPowerSeriesParameterData
import Dubon2026.AuxiliaryFamilyAugmentationRepresentation

/-! The original ring comparison and its power-series map retain the
same character family. The variable-ideal quotient therefore recovers
the actual base ring and all original universal matrices, as required
by the coefficient comparison in DUB-17's arithmetic patching system. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- Constructed power-series parameters coupled to the original
augmentation comparison through their identical character family. -/
structure AuxiliaryPowerSeriesAugmentationComparison
    (O : Type*) [CommRing O] {R A ι n G : Type*}
    [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
    [Fintype ι] [Fintype n] [DecidableEq n]
    (Q : Finset Nat.Primes) (q : ℕ)
    (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A) where
  /-- The constructed original character family and full coefficient comparison. -/
  augmentation : AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι)
    (fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q) τ τ₀
  /-- Power-series data for that exact character family. -/
  parameters : AuxiliaryPowerSeriesParameterData O Q q augmentation.characters

variable (O : Type*) [CommRing O] {R A ι n G : Type*}
  [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
  [Fintype ι] [Fintype n] [DecidableEq n]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- Construct the parameter map for the actual characters returned by
the original augmentation comparison. -/
def completeLocalAuxiliaryPowerSeriesAugmentationComparison
    [IsAdicComplete (maximalIdeal R) R]
    (c : AuxiliaryFamilyAugmentationRepresentationComparison O (ι := ι)
      (fun p : Q => RationalPrimeTameCoefficientQuotient p.val.val q) τ τ₀) :
    AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀ where
  augmentation := c
  parameters := completeLocalAuxiliaryPowerSeriesParameterData O Q q c.characters c.residue_one

/-- The image of the power-series variable ideal gives the original
base coefficient ring under the constructed augmentation comparison. -/
def auxiliaryPowerSeriesAugmentationQuotientEquiv
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀) :
    (R ⧸ Ideal.map d.parameters.parameterMap.toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι))))) ≃ₐ[O] A :=
  (Ideal.quotientEquivAlgOfEq O d.parameters.augmentation).trans d.augmentation.equiv

/-- The power-series augmentation quotient preserves every original
universal matrix under the same base-ring comparison. -/
theorem auxiliaryPowerSeriesAugmentationQuotientEquiv_matrix
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀) (g : G) :
    GeneralLinearGroup.map
      (auxiliaryPowerSeriesAugmentationQuotientEquiv O Q q τ τ₀ d).toAlgHom.toRingHom
      (GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.map d.parameters.parameterMap.toRingHom
          (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι)))))) (τ g)) = τ₀ g := by
  let J := Ideal.map d.parameters.parameterMap.toRingHom
    (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι))))
  let K := auxiliaryFamilyAugmentationIdeal O d.augmentation.characters
  let e := Ideal.quotientEquivAlgOfEq O d.parameters.augmentation
  have he : GeneralLinearGroup.map e.toAlgHom.toRingHom
      (GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g)) =
      GeneralLinearGroup.map (Ideal.Quotient.mk K) (τ g) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact Ideal.quotientEquivAlgOfEq_mk O d.parameters.augmentation ((τ g).val i j)
  change GeneralLinearGroup.map (d.augmentation.equiv.toAlgHom.toRingHom.comp e.toAlgHom.toRingHom)
    (GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g)) = τ₀ g
  rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, he]
  exact d.augmentation.matrix g

end
end Dubon2026
