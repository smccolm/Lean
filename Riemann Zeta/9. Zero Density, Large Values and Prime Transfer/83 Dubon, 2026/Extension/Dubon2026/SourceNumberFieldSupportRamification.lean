import Dubon2026.OriginalIntegerPrimeTower
import Dubon2026.ArithmeticAuxiliarySupportRamification

/-! DUB-17/18 -> arithmetic quotient -> actual finite-field containment.
The existing classification of integer primes converts unramifiedness
at each rational prime outside the support into the exact original
height-one-prime criterion for the arithmetic union. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

theorem numberField_support_ramification_of_rational_unramified
    (F : Type) [Field F] [NumberField F] (a : ℕ)
    (hU : ∀ p : ℕ, p.Prime → ¬p ∣ a →
      Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p : 𝓞 ℚ)}))
    (w : HeightOneSpectrum (𝓞 F)) (hwa : (a : 𝓞 F) ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
  obtain ⟨p, hp, hw⟩ := originalIntegerPrimeBelow_exists_prime F w
  have hpm : (p : 𝓞 F) ∈ w.asIdeal := by
    have hm : (p : ℤ) ∈ w.asIdeal.under ℤ := by
      rw [← hw.over]
      exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [Ideal.mem_under, map_natCast] using hm
  have hpa : ¬p ∣ a := by
    intro h
    obtain ⟨b, rfl⟩ := h
    apply hwa
    rw [Nat.cast_mul]
    exact w.asIdeal.mul_mem_right _ hpm
  let v := rationalOriginalPrimePlace p hp
  letI : w.asIdeal.IsPrime := w.isPrime
  have hle : v.asIdeal ≤ w.asIdeal.under (𝓞 ℚ) := by
    rw [rationalOriginalPrimePlace_eq_span, Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal
    simpa only [map_natCast] using hpm
  letI : w.asIdeal.LiesOver v.asIdeal :=
    ⟨v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
  have hu : Chebotarev.UnramifiedIn ℚ F v.asIdeal := by
    simpa only [v, rationalOriginalPrimePlace_eq_span] using hU p hp hpa
  letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := hu.2 w.asIdeal w.isMaximal inferInstance
  rw [← Ideal.over_def w.asIdeal v.asIdeal]
  exact (numberField_isUnramifiedAt_iff_ramificationIdx_one v w).mp inferInstance

end
end Dubon2026
