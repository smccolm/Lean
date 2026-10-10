import Dubon2026.NumberFieldRamificationUnramified
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Locus

/-! # Actual number-field unramifiedness after inverting the original exceptional element -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField nonZeroDivisors

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- The generic prime of the original number-field integer ring is unramified over the original base integer ring, using the actual separable field extension. -/
theorem numberField_isUnramifiedAt_bot :
    Algebra.IsUnramifiedAt (𝓞 K) (⊥ : Ideal (𝓞 L)) := by
  letI : Algebra.FormallyUnramified (𝓞 K) K :=
    Algebra.FormallyUnramified.of_isLocalization (Rₘ := K) (𝓞 K)⁰
  letI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  letI : Algebra.FormallyUnramified (𝓞 K) L :=
    Algebra.FormallyUnramified.comp (𝓞 K) K L
  letI : IsLocalization (⊥ : Ideal (𝓞 L)).primeCompl L := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  exact Algebra.FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv (⊥ : Ideal (𝓞 L)).primeCompl L
      (Localization.AtPrime (⊥ : Ideal (𝓞 L)))).restrictScalars (𝓞 K))

/-- Literal index-one conditions at every original finite prime outside the exceptional element imply formal unramifiedness of the actual away-localized integer ring. The generic prime is discharged from actual field separability. -/
theorem numberField_formallyUnramified_away
    (a : 𝓞 K)
    (hunram : ∀ w : HeightOneSpectrum (𝓞 L), algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    Algebra.FormallyUnramified (𝓞 K)
      (Localization.Away (algebraMap (𝓞 K) (𝓞 L) a)) := by
  apply Algebra.basicOpen_subset_unramifiedLocus_iff.mp
  intro p hp
  change Algebra.IsUnramifiedAt (𝓞 K) p.asIdeal
  by_cases hzero : p.asIdeal = ⊥
  · simpa only [hzero] using numberField_isUnramifiedAt_bot (K := K) (L := L)
  · let w : HeightOneSpectrum (𝓞 L) := ⟨p.asIdeal, p.isPrime, hzero⟩
    have hw : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
      (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
        (R := 𝓞 K) (p := w.asIdeal) w.ne_bot).mpr (hunram w hp)
    exact hw

end
end Dubon2026
