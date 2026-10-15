import Dubon2026.LocalizedUnitKummerAlgebra
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! # Localizing an actual valuation unit away from its original prime

A unit at one original finite prime becomes an actual unit of a localized
integer ring whose denominator avoids that prime and contains the prescribed
exponent. This permits reuse of the proved localized-unit Kummer algebra for
the q-primary source-class comparison in DUB-17; no ramification conclusion
or global principalization is assumed here.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K]

/-- An actual valuation unit is a unit in an original localization away from the same prime, with the prescribed prime-avoiding integer inverted. -/
theorem originalValuationUnit_exists_localization
    (v : HeightOneSpectrum (𝓞 K)) (q : ℕ) (hq : (q : 𝓞 K) ∉ v.asIdeal)
    (u : Kˣ) (hu : v.valuation K (u : K) = 1) :
    ∃ (b : 𝓞 K) (hb : b ≠ 0), b ∉ v.asIdeal ∧ (q : 𝓞 K) ∣ b ∧
      ∃ z : (originalLocalizedIntegers K b hb)ˣ, z.val.val = (u : K) := by
  obtain ⟨r, d, hrd⟩ := v.exists_primeCompl_mul_eq_of_integer (u : K) hu.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.property
  have hr : r ∉ v.asIdeal := by
    apply (v.valuation_eq_one_iff_notMem (K := K)).mp
    rw [← hrd, map_mul, hu, one_mul]
    exact (v.valuation_eq_one_iff_notMem (K := K)).mpr hd
  let b : 𝓞 K := q * r * d
  have hbmem : b ∉ v.asIdeal :=
    v.isPrime.mul_notMem (v.isPrime.mul_notMem hq hr) hd
  have hb : b ≠ 0 := fun h => hbmem (h.symm ▸ v.asIdeal.zero_mem)
  let R := originalLocalizedIntegers K b hb
  have hrb : r ∣ b := dvd_mul_of_dvd_left (dvd_mul_left r (q : 𝓞 K)) d
  have hdb : (d : 𝓞 K) ∣ b := dvd_mul_left (d : 𝓞 K) ((q : 𝓞 K) * r)
  have hrU : IsUnit (algebraMap (𝓞 K) R r) := IsLocalization.Away.isUnit_of_dvd b hrb
  have hdU : IsUnit (algebraMap (𝓞 K) R d) := IsLocalization.Away.isUnit_of_dvd b hdb
  let z : Rˣ := hrU.unit / hdU.unit
  refine ⟨b, hb, hbmem, dvd_mul_of_dvd_left (dvd_mul_right (q : 𝓞 K) r) d, z, ?_⟩
  have hzd : z.val * algebraMap (𝓞 K) R d = algebraMap (𝓞 K) R r := by
    rw [← hdU.unit_spec, ← hrU.unit_spec]
    exact congrArg Units.val (div_mul_cancel hrU.unit hdU.unit)
  have he := congrArg (fun t : R => t.val) hzd
  change z.val.val * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K r at he
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    intro h
    have hz : (d : 𝓞 K) = 0 := Subtype.ext h
    exact hd (hz.symm ▸ v.asIdeal.zero_mem)
  exact mul_right_cancel₀ hd0 (he.trans hrd.symm)

end
end Dubon2026
