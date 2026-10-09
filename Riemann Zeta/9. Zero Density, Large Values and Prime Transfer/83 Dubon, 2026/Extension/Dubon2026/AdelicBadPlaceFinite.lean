import Dubon2026.AdelicGoodPlaceEnumeration
import Mathlib.Data.Nat.PrimeFin

/-! # The genuine bad finite places are exactly the finitely many original level prime divisors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The prime-place correspondence reconstructs each actual finite place from its genuine ordinary prime generator. -/
theorem rationalPrimePlace_natGenerator_eq (v : HeightOneSpectrum ℤ) :
    rationalPrimePlace (Rat.HeightOneSpectrum.natGenerator v) (Rat.HeightOneSpectrum.prime_natGenerator v) = v :=
  Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply v

/-- The actual ordinary prime generator distinguishes genuine finite places. -/
theorem finitePlace_natGenerator_injective :
    Function.Injective (fun v : HeightOneSpectrum ℤ => Rat.HeightOneSpectrum.natGenerator v) := by
  intro v w he
  apply Rat.HeightOneSpectrum.primesEquiv.injective
  exact Subtype.ext he

/-- Goodness is exactly coprimality of the original place's actual ordinary prime generator with the level. -/
theorem isGoodAdelicPlace_iff_coprime (N : ℕ) (v : HeightOneSpectrum ℤ) :
    IsGoodAdelicPlace N v ↔ (Rat.HeightOneSpectrum.natGenerator v).Coprime N := by
  constructor
  · rintro ⟨p, hp, hc, rfl⟩
    simpa only [rationalPrimePlace_natGenerator] using hc
  · intro hc
    exact ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v,
      hc, (rationalPrimePlace_natGenerator_eq v).symm⟩

/-- A genuine finite place is bad exactly when its original prime generator divides the original level. -/
theorem not_isGoodAdelicPlace_iff_dvd (N : ℕ) (v : HeightOneSpectrum ℤ) :
    ¬ IsGoodAdelicPlace N v ↔ Rat.HeightOneSpectrum.natGenerator v ∣ N := by
  rw [isGoodAdelicPlace_iff_coprime, (Rat.HeightOneSpectrum.prime_natGenerator v).coprime_iff_not_dvd, not_not]

/-- The actual bad finite places of the original level. -/
abbrev AdelicBadPlace (N : ℕ) := {v : HeightOneSpectrum ℤ // ¬ IsGoodAdelicPlace N v}

/-- Each actual bad finite place determines a genuine member of the finite original level prime-factor set. -/
def adelicBadPlacePrimeFactor (N : ℕ) [NeZero N] (v : AdelicBadPlace N) : ↥N.primeFactors :=
  ⟨Rat.HeightOneSpectrum.natGenerator v.val,
    Nat.mem_primeFactors.mpr ⟨Rat.HeightOneSpectrum.prime_natGenerator v.val,
      (not_isGoodAdelicPlace_iff_dvd N v.val).mp v.property, NeZero.ne N⟩⟩

/-- The genuine level-prime-factor encoding of actual bad finite places is injective. -/
theorem adelicBadPlacePrimeFactor_injective (N : ℕ) [NeZero N] : Function.Injective (adelicBadPlacePrimeFactor N) := by
  intro v w he
  apply Subtype.ext
  apply finitePlace_natGenerator_injective
  exact congrArg Subtype.val he

/-- The original bad-place type is genuinely finite because its prime generators divide the positive original level. -/
instance adelicBadPlaceFinite (N : ℕ) [NeZero N] : Finite (AdelicBadPlace N) :=
  Finite.of_injective (adelicBadPlacePrimeFactor N) (adelicBadPlacePrimeFactor_injective N)

/-- The actual finite family of original bad places can therefore be used in genuine finite tensor and group constructions. -/
instance adelicBadPlaceFintype (N : ℕ) [NeZero N] : Fintype (AdelicBadPlace N) := Fintype.ofFinite _

end
end Dubon2026
