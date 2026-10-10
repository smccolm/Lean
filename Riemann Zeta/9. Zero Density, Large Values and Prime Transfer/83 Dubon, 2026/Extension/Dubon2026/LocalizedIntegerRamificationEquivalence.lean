import Dubon2026.NumberFieldLocalizedIntegerAlgebras

/-! # The exact original ramification conditions of the actual localized integer algebra -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- Formal unramifiedness of the actual compatible localized integer algebra is equivalent to index one at every original finite prime outside the original exceptional element. -/
theorem numberField_localizedIntegers_unramified_iff
    (a : 𝓞 K) (Rₐ Sₐ : Type*) [CommRing Rₐ] [CommRing Sₐ]
    [Algebra (𝓞 K) Rₐ] [Algebra (𝓞 K) Sₐ] [Algebra (𝓞 L) Sₐ]
    [Algebra Rₐ Sₐ] [IsScalarTower (𝓞 K) (𝓞 L) Sₐ]
    [IsScalarTower (𝓞 K) Rₐ Sₐ]
    [IsLocalization.Away a Rₐ]
    [IsLocalization.Away (algebraMap (𝓞 K) (𝓞 L) a) Sₐ] :
    Algebra.FormallyUnramified Rₐ Sₐ ↔
      ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  constructor
  · intro h
    letI := h
    letI : Algebra.FormallyUnramified (𝓞 K) Rₐ :=
      Algebra.FormallyUnramified.of_isLocalization (Rₘ := Rₐ) (.powers a)
    letI : Algebra.FormallyUnramified (𝓞 K) Sₐ :=
      Algebra.FormallyUnramified.comp (𝓞 K) Rₐ Sₐ
    letI : Algebra.FormallyUnramified (𝓞 K)
        (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a)) :=
      Algebra.FormallyUnramified.of_equiv
        ((IsLocalization.algEquiv (.powers (algebraMap (𝓞 K) (𝓞 L) a)) Sₐ
          (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a))).restrictScalars (𝓞 K))
    have hopen := (Algebra.basicOpen_subset_unramifiedLocus_iff
      (R := 𝓞 K) (f := algebraMap (𝓞 K) (𝓞 L) a)).mpr inferInstance
    intro w hw
    apply (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := 𝓞 K) (p := w.asIdeal) w.ne_bot).mp
    exact hopen (show (⟨w.asIdeal, w.isPrime⟩ : PrimeSpectrum (𝓞 L)) ∈
      PrimeSpectrum.basicOpen (algebraMap (𝓞 K) (𝓞 L) a) from hw)
  · intro h
    exact (numberField_localizedIntegers_finite_unramified a Rₐ Sₐ h).2

end
end Dubon2026
