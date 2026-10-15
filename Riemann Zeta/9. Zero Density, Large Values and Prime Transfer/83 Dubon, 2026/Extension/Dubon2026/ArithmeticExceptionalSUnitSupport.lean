import Dubon2026.LocalizedIntegerSUnitComparison
import Dubon2026.SupportedIdeleCohomologySequence

/-! # The exact finite S-unit support used by the arithmetic idele sequence

The fixed exceptional integer supplies the original finite Galois-stable support.
The localized S-units are identified with precisely these supported coefficients.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable (L : Type) [Field L] [NumberField L] (b : 𝓞 L) (hb : b ≠ 0)

include hb in
/-- The exact set of primes containing the exceptional integer is finite. -/
theorem originalExceptionalIntegerSupport_finite :
    {w : HeightOneSpectrum (𝓞 L) | b ∈ w.asIdeal}.Finite := by
  simpa only [Ideal.dvd_span_singleton] using
    (Ideal.finite_factors (I := Ideal.span {b}) (by simpa using hb))

/-- The original exceptional prime set, retaining exactly the primes containing the chosen integer. -/
def originalExceptionalIntegerSupport : Finset (HeightOneSpectrum (𝓞 L)) :=
  (originalExceptionalIntegerSupport_finite L b hb).toFinset

/-- Membership is literal containment of the same original exceptional integer. -/
theorem mem_originalExceptionalIntegerSupport (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ originalExceptionalIntegerSupport L b hb ↔ b ∈ w.asIdeal :=
  (originalExceptionalIntegerSupport_finite L b hb).mem_toFinset

/-- The actual finite support gives exactly the existing supported-idele S-unit coefficient. -/
def originalLocalizedUnitsEquivSupportedSUnits :
    (originalLocalizedIntegers L b hb)ˣ ≃*
      (↑(originalExceptionalIntegerSupport L b hb) : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  have hS : (↑(originalExceptionalIntegerSupport L b hb) : Set (HeightOneSpectrum (𝓞 L))) =
      {w | b ∈ w.asIdeal} := by
    ext w
    exact mem_originalExceptionalIntegerSupport L b hb w
  exact (originalLocalizedUnitsEquivSUnits L b hb).trans
    (MulEquiv.subgroupCongr (congrArg (fun S : Set (HeightOneSpectrum (𝓞 L)) => S.unit L) hS.symm))

/-- The finite-supported unit comparison preserves the original ambient field value. -/
theorem originalLocalizedUnitsEquivSupportedSUnits_coe
    (u : (originalLocalizedIntegers L b hb)ˣ) :
    ((originalLocalizedUnitsEquivSupportedSUnits L b hb u).val : L) = u.val.val := by
  exact originalLocalizedUnitsEquivSUnits_coe L b hb u

variable (K : Type) [Field K] [Algebra K L]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The same original exceptional support is stable under the actual Galois action. -/
theorem originalExceptionalIntegerSupport_galoisStable
    (σ : Gal(L/K)) (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
        (originalIntegerMap_ne_zero (L := L) a ha) ↔
      numberFieldGaloisPlaceEquiv K L σ w ∈
        originalExceptionalIntegerSupport L (algebraMap (𝓞 K) (𝓞 L) a)
          (originalIntegerMap_ne_zero (L := L) a ha) := by
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  change algebraMap (𝓞 K) (𝓞 L) a ∈ w.asIdeal ↔
    NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
      (algebraMap (𝓞 K) (𝓞 L) a) ∈ w.asIdeal
  have hfix : NumberField.RingOfIntegers.mapRingHom σ.symm.toRingHom
      (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
    apply NumberField.RingOfIntegers.ext
    exact σ.symm.commutes a.val
  rw [hfix]

end
end Dubon2026
