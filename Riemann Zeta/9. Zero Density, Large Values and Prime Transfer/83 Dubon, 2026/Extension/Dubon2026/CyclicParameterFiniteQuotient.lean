import Dubon2026.ScalarPrimePowerCongruence
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! A genuine cyclic auxiliary group maps to the units of a finite
parameter quotient when its order has the required prime-power divisor.
This realizes the finite-level factorization needed for the DUB-17
patching annihilator condition; no annihilator estimate is assumed. -/

namespace Dubon2026
noncomputable section

/-- Construct the cyclic character sending its chosen generator to
the actual residue-one scalar in the ideal-power quotient. -/
def cyclicParameterQuotientCharacter
    {R D : Type*} [CommRing R] [Group D]
    (I : Ideal R) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I)
    (g : D) (hg : ∀ d, d ∈ Subgroup.zpowers g)
    (x : R) (hx : x - 1 ∈ I) (n : ℕ) (hd : q ^ n ∣ orderOf g) :
    D →* (R ⧸ I ^ n)ˣ :=
  let hpow := scalar_primePower_quotient_eq_one I hq hqI x hx n
  let u := Units.ofPowEqOne (Ideal.Quotient.mk (I ^ n) x) (q ^ n)
    hpow (pow_ne_zero _ hq.ne_zero)
  monoidHomOfForallMemZpowers hg
    ((orderOf_dvd_of_pow_eq_one (Units.pow_ofPowEqOne hpow
      (pow_ne_zero _ hq.ne_zero))).trans hd : orderOf u ∣ orderOf g)

/-- The constructed character has the required original generator
value, rather than merely an abstract existence property. -/
theorem cyclicParameterQuotientCharacter_generator
    {R D : Type*} [CommRing R] [Group D]
    (I : Ideal R) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I)
    (g : D) (hg : ∀ d, d ∈ Subgroup.zpowers g)
    (x : R) (hx : x - 1 ∈ I) (n : ℕ) (hd : q ^ n ∣ orderOf g) :
    (cyclicParameterQuotientCharacter I hq hqI g hg x hx n hd g).val =
      Ideal.Quotient.mk (I ^ n) x := by
  simp only [cyclicParameterQuotientCharacter,
    monoidHomOfForallMemZpowers_apply_gen, Units.val_ofPowEqOne]

end
end Dubon2026
