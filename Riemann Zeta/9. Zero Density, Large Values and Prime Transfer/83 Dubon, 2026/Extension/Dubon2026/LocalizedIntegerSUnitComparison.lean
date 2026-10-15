import Dubon2026.CanonicalLocalizedIntegerMaps
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Original localized integers and the valuation-defined S-units

This identifies the finite-stage coefficient objects used in arithmetic S-unit
divisibility with the actual S-unit objects in the original supported-idele
sequence, for precisely the primes containing the exceptional integer.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

private theorem valuation_power_clears_denominator
    (v : WithZero (Multiplicative ℤ)) (hv : v ≠ 0) (hv1 : v < 1)
    (w : WithZero (Multiplicative ℤ)) (hw : w ≠ 0)
    (n : ℕ) (hn : WithZero.log w ≤ (n : ℤ)) : v ^ n * w ≤ 1 := by
  apply (WithZero.log_le_log (mul_ne_zero (pow_ne_zero n hv) hw) one_ne_zero).mp
  rw [WithZero.log_mul (pow_ne_zero n hv) hw, WithZero.log_pow, WithZero.log_one,
    nsmul_eq_mul]
  have hneg : WithZero.log v < 0 := by
    simpa only [WithZero.log_one] using (WithZero.log_lt_log hv one_ne_zero).mpr hv1
  have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
  nlinarith

variable (K : Type) [Field K] [NumberField K] (a : 𝓞 K) (ha : a ≠ 0)

/-- An actual localized integer has valuation at most one at every original prime away from a. -/
theorem originalLocalizedInteger_valuation_le_one
    (x : originalLocalizedIntegers K a ha) (v : HeightOneSpectrum (𝓞 K))
    (hv : a ∉ v.asIdeal) : v.valuation K x.val ≤ 1 := by
  obtain ⟨r, s, hs, hx⟩ := x.property
  obtain ⟨n, rfl⟩ := hs
  rw [hx, map_mul, map_inv₀, map_pow, map_pow, (v.valuation_eq_one_iff_notMem).mpr hv,
    one_pow, inv_one, mul_one]
  exact v.valuation_le_one r

include ha in
/-- The original denominator can be cleared by one actual power of a when all away valuations are integral. -/
theorem originalSInteger_exists_power_denominator (x : K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), a ∉ v.asIdeal → v.valuation K x ≤ 1) :
    ∃ n : ℕ, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K a) ^ n * x := by
  classical
  by_cases hx0 : x = 0
  · exact ⟨0, 0, by simp [hx0]⟩
  let T := (HeightOneSpectrum.Support.finite (𝓞 K) x).toFinset
  let n := T.sup fun v => (WithZero.log (v.valuation K x)).toNat
  refine ⟨n, HeightOneSpectrum.mem_integers_of_valuation_le_one K _ ?_⟩
  intro v
  rw [map_mul, map_pow]
  by_cases hv : v ∈ T
  · have hbad : 1 < v.valuation K x :=
      (HeightOneSpectrum.Support.finite (𝓞 K) x).mem_toFinset.mp hv
    have hva : a ∈ v.asIdeal := by
      by_contra h
      exact (not_le_of_gt hbad) (hx v h)
    apply valuation_power_clears_denominator
      (v.valuation K (algebraMap (𝓞 K) K a))
      ((Valuation.ne_zero_iff _).mpr ((IsFractionRing.injective (𝓞 K) K).ne ha))
      ((v.valuation_lt_one_iff_mem a).mpr hva)
      (v.valuation K x) ((Valuation.ne_zero_iff _).mpr hx0) n
    exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr
      (Finset.le_sup (f := fun w => (WithZero.log (w.valuation K x)).toNat) hv))
  · have hgood : v.valuation K x ≤ 1 := le_of_not_gt fun h =>
      hv ((HeightOneSpectrum.Support.finite (𝓞 K) x).mem_toFinset.mpr h)
    exact mul_le_one₀ (pow_le_one₀ zero_le (v.valuation_le_one a))
      zero_le hgood

/-- The original localized integer ring equals the valuation-defined S-integer ring for exactly the same primes. -/
theorem originalLocalizedIntegers_eq_SIntegers :
    originalLocalizedIntegers K a ha =
      ({v : HeightOneSpectrum (𝓞 K) | a ∈ v.asIdeal} : Set _).integer K := by
  ext x
  constructor
  · intro hx v hv
    exact originalLocalizedInteger_valuation_le_one K a ha ⟨x, hx⟩ v hv
  · intro hx
    obtain ⟨n, r, hr⟩ := originalSInteger_exists_power_denominator K a ha x hx
    refine ⟨r, a ^ n, ⟨n, rfl⟩, ?_⟩
    rw [map_pow, hr]
    have haK : algebraMap (𝓞 K) K a ≠ 0 := (IsFractionRing.injective (𝓞 K) K).ne ha
    field_simp

/-- The two genuine finite-stage S-unit groups are equivalent through the proved ring equality. -/
def originalLocalizedUnitsEquivSUnits :
    (originalLocalizedIntegers K a ha)ˣ ≃*
      ({v : HeightOneSpectrum (𝓞 K) | a ∈ v.asIdeal} : Set _).unit K :=
  (Units.mapEquiv (Subalgebra.equivOfEq _ _
    (originalLocalizedIntegers_eq_SIntegers K a ha)).toMulEquiv).trans
    (Set.unitEquivUnitsInteger _ K).symm

/-- The actual finite-stage unit identification leaves its original field value unchanged. -/
theorem originalLocalizedUnitsEquivSUnits_coe
    (u : (originalLocalizedIntegers K a ha)ˣ) :
    ((originalLocalizedUnitsEquivSUnits K a ha u).val : K) = u.val.val := by
  rfl

end
end Dubon2026
