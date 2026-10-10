import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # The actual localized integer ring inside the original number field -/

namespace Dubon2026

noncomputable section
open scoped NumberField nonZeroDivisors

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Genuine compatible localizations of the original integer rings retain the actual integral closure inside the original number field. -/
theorem localizedNumberFieldIntegers_isIntegralClosure
    (a : 𝓞 K) (ha : a ≠ 0) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ]
    [Algebra Rₐ L] [Algebra Sₐ L] [IsScalarTower (𝓞 L) Sₐ L]
    [IsScalarTower Rₐ Sₐ L] : IsIntegralClosure Sₐ Rₐ L := by
  have haL : algebraMap (𝓞 K) (𝓞 L) a ≠ 0 := by
    intro h
    apply ha
    apply NumberField.RingOfIntegers.algebraMap.injective K L
    simpa only [map_zero] using h
  let M := Submonoid.powers (algebraMap (𝓞 K) (𝓞 L) a)
  have hM : M ≤ (𝓞 L)⁰ := powers_le_nonZeroDivisors_of_noZeroDivisors haL
  letI : IsDomain Sₐ := IsLocalization.isDomain_of_le_nonZeroDivisors Sₐ hM
  letI : IsIntegrallyClosed Sₐ := isIntegrallyClosed_of_isLocalization Sₐ M hM
  letI : IsFractionRing Sₐ L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Sₐ L
  letI : Module.Finite Rₐ Sₐ :=
    Module.Finite.of_isLocalization (𝓞 K) (𝓞 L) (.powers a)
  exact IsIntegralClosure.of_isIntegrallyClosed Sₐ Rₐ L

/-- In the original number field, being integral over the actual localized base is equivalent to being the image of an original localized integer. -/
theorem localizedNumberFieldIntegers_integral_iff
    (a : 𝓞 K) (ha : a ≠ 0) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ]
    [Algebra Rₐ L] [Algebra Sₐ L] [IsScalarTower (𝓞 L) Sₐ L]
    [IsScalarTower Rₐ Sₐ L] (x : L) :
    IsIntegral Rₐ x ↔ ∃ y : Sₐ, algebraMap Sₐ L y = x := by
  letI := localizedNumberFieldIntegers_isIntegralClosure (L := L) a ha Rₐ Sₐ
  exact IsIntegralClosure.isIntegral_iff

end
end Dubon2026
