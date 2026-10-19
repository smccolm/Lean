import Dubon2026.CompleteLocalAuxiliaryPowerSeries

/-! Constructed power-series data for the actual tame characters.
The record preserves the generators and coefficient map needed when
the common parameter algebra acts on arithmetic deformation rings. -/

namespace Dubon2026
noncomputable section
open IsLocalRing

/-- Output of the proved complete-local parameter construction for
the displayed original tame character family. -/
structure AuxiliaryPowerSeriesParameterData
    (O : Type*) [CommRing O] {ι A : Type*}
    [Fintype ι] [CommRing A] [Algebra O A]
    (Q : Finset Nat.Primes) (q : ℕ)
    (κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (ι → A)ˣ) where
  /-- Constructed generators of the actual tame quotient groups. -/
  generators : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q
  /-- Every original tame quotient element is a nonnegative power of its generator. -/
  generates : ∀ p d, ∃ n : ℕ, generators p ^ n = d
  /-- The constructed power-series algebra map to the original coefficient ring. -/
  parameterMap : MvPowerSeries (Q × ι) O →ₐ[O] A
  /-- Every variable is the corresponding original character difference. -/
  variableValue : ∀ pi : Q × ι,
    parameterMap (MvPowerSeries.X pi) = ((κ pi.1 (generators pi.1)).val pi.2) - 1
  /-- The variable ideal has exactly the original character augmentation image. -/
  augmentation : Ideal.map parameterMap.toRingHom
    (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := Q × ι)))) =
      auxiliaryFamilyAugmentationIdeal O κ

/-- Construct the full parameter data from adic completeness and the
proved residue-one property of the original characters. -/
def completeLocalAuxiliaryPowerSeriesParameterData
    (O : Type*) [CommRing O] {ι A : Type*}
    [Fintype ι] [CommRing A] [IsLocalRing A] [Algebra O A]
    [IsAdicComplete (maximalIdeal A) A]
    (Q : Finset Nat.Primes) (q : ℕ)
    (κ : ∀ p : Q, RationalPrimeTameCoefficientQuotient p.val.val q →* (ι → A)ˣ)
    (hκ : ∀ p d i, residue A ((κ p d).val i) = 1) :
    AuxiliaryPowerSeriesParameterData O Q q κ :=
  let h := completeLocalAuxiliaryFamily_exists_powerSeries_parameters O Q q κ hκ
  let g := Classical.choose h
  let hg := Classical.choose_spec h
  let e := Classical.choose hg
  let he := Classical.choose_spec hg
  ⟨g, he.1, e, he.2.1, he.2.2⟩

end
end Dubon2026
