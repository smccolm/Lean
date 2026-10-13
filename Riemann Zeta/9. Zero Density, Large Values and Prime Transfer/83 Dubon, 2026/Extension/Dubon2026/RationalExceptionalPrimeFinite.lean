import Dubon2026.RationalPrimeLocalizedIntegerUnits
import Mathlib.Data.Set.Finite.Basic

/-! # Finiteness of the original rational exceptional prime set

The literal integer-ring divisibility condition used by arithmetic H2 support
is transported through the existing rational ring-of-integers equivalence.
This supplies the finite index set required by DUB-17's local invariant sum.
-/

namespace Dubon2026
open scoped NumberField

/-- Only finitely many original rational primes divide the actual nonzero
exceptional integer; no independent exceptional-prime finiteness is assumed. -/
theorem rationalExceptionalPrimeSet_finite (a : 𝓞 ℚ) (ha : a ≠ 0) :
    {p : Nat.Primes | (p.val : 𝓞 ℚ) ∣ a}.Finite := by
  let e := Rat.ringOfIntegersEquiv
  have hz : e a ≠ 0 := fun h => ha (e.injective (h.trans (map_zero e).symm))
  have hf := (Set.finite_le_nat (e a).natAbs).preimage
    (f := fun p : Nat.Primes => p.val) Subtype.val_injective.injOn
  apply hf.subset
  intro p hp
  have hd := map_dvd e.toRingHom hp
  change e (p.val : 𝓞 ℚ) ∣ e a at hd
  rw [map_natCast] at hd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hz) (Int.natCast_dvd.mp hd)

end Dubon2026
