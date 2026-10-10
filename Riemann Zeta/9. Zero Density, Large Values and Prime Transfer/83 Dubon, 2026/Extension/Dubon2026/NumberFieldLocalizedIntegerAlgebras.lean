import Dubon2026.NumberFieldUnramifiedAway
import Mathlib.RingTheory.Localization.Finiteness

/-! # Actual finite unramified integer algebras over the original localized base -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Actual compatible localizations of the original integer rings form a finite formally unramified algebra over the localized base when the original remaining finite-prime indices are one. Both conclusions are derived from the original rings and their literal localization maps. -/
theorem numberField_localizedIntegers_finite_unramified
    (a : 𝓞 K) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ]
    (hunram : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    Module.Finite Rₐ Sₐ ∧ Algebra.FormallyUnramified Rₐ Sₐ := by
  letI : Algebra.FormallyUnramified (𝓞 K)
      (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a)) :=
    numberField_formallyUnramified_away a hunram
  letI : Algebra.FormallyUnramified (𝓞 K) Sₐ :=
    Algebra.FormallyUnramified.of_equiv
      ((IsLocalization.algEquiv (.powers (algebraMap (𝓞 K) (𝓞 L) a))
        (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a)) Sₐ).restrictScalars (𝓞 K))
  exact ⟨Module.Finite.of_isLocalization (𝓞 K) (𝓞 L) (.powers a),
    Algebra.FormallyUnramified.of_restrictScalars (𝓞 K) Rₐ Sₐ⟩

end
end Dubon2026
