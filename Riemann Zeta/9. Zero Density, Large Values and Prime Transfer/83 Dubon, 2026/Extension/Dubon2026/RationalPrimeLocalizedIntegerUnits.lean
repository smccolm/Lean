import Dubon2026.OriginalLocalizedIntegerLocalMap
import Dubon2026.FinitePlaceIntegerUnits
import Dubon2026.RationalPrimeRootH2Invariant

/-! # The original exceptional integer is a unit at every required local prime

The existing adic unit construction is transported to the same valuation ring
used by local duality, discharging the coefficient-map premise for actual
unramified base change and DUB-17 local-invariant support.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel WithZero

variable (p : ℕ) (hp : p.Prime)

/-- The canonical valuation integer ring is the original adic integer ring,
with equality of the actual subsets of the same original local field. -/
theorem rationalPrimeLocalInteger_subring_eq :
    (ValuativeRel.valuation (rationalPrimeLocalField p hp)).integer =
      (rationalPrimeLocalIntegerRing p hp).toSubring := by
  apply Subring.ext
  intro x
  change (ValuativeRel.valuation (rationalPrimeLocalField p hp)) x ≤ 1 ↔
    (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰)) x ≤ 1
  rw [← (ValuativeRel.valuation (rationalPrimeLocalField p hp)).vle_one_iff,
    ← (Valued.v (R := rationalPrimeLocalField p hp) (Γ₀ := ℤᵐ⁰)).vle_one_iff]

/-- The original integer away from p is a unit in the original local-duality
valuation ring, by the already constructed actual adic unit. -/
theorem rationalPrimeValuationInteger_isUnit_int (z : ℤ) (hz : ¬(p : ℤ) ∣ z) :
    IsUnit (z : 𝒪[rationalPrimeLocalField p hp]) := by
  obtain ⟨u, hu⟩ := rationalPrimePlace_integer_unit p hp z hz
  rw [rationalPrimeLocalInteger_subring_eq]
  have he : u.val = (z : rationalPrimeLocalIntegerRing p hp) := Subtype.ext hu
  exact he ▸ u.isUnit

/-- Nondivisibility in the original rational integer ring supplies the actual
unit needed to extend that same ring map to the original localized integers. -/
theorem rationalPrimeOriginalInteger_isUnit (a : 𝓞 ℚ) (ha : ¬(p : 𝓞 ℚ) ∣ a) :
    IsUnit (originalIntegerToValuationIntegerMap ℚ (rationalPrimeLocalField p hp) a) := by
  let e := Rat.ringOfIntegersEquiv
  let z : ℤ := e a
  have hz : (z : 𝓞 ℚ) = a :=
    (map_intCast e.symm z).symm.trans (e.symm_apply_apply a)
  have hzaway : ¬(p : ℤ) ∣ z := by
    intro hd
    apply ha
    have he := map_dvd e.symm.toRingHom hd
    change e.symm (p : ℤ) ∣ e.symm (e a) at he
    simpa only [map_natCast, e.symm_apply_apply] using he
  rw [← hz, map_intCast]
  exact rationalPrimeValuationInteger_isUnit_int p hp z hzaway

end
end Dubon2026
