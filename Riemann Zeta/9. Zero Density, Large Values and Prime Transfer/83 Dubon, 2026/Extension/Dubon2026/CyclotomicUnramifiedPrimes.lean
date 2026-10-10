import Dubon2026.NumberFieldRamificationUnramified
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.Ideal.NatInt

/-! # Original rational cyclotomic primes outside the conductor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- For a genuine rational cyclotomic field, the original integer prime outside the conductor has ramification index one over the actual rational integer ring. -/
theorem rationalCyclotomic_ramificationIdx_one
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ F]
    (w : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ w.asIdeal) :
    (w.asIdeal.under ℤ).ramificationIdx w.asIdeal = 1 := by
  let v := w.under ℤ
  letI : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under ℤ))
  obtain ⟨p, hp, hv⟩ :=
    (Ideal.isPrime_int_iff.mp v.isPrime).resolve_left v.ne_bot
  letI : Fact p.Prime := ⟨hp⟩
  letI : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [← hv]
    infer_instance
  have hpm : ¬p ∣ m := by
    intro hdiv
    have hmem : (m : ℤ) ∈ v.asIdeal := by
      rw [hv, Ideal.mem_span_singleton]
      exact_mod_cast hdiv
    have hmem' := (Ideal.mem_of_liesOver w.asIdeal v.asIdeal (m : ℤ)).mp hmem
    exact hm (by simpa only [map_natCast, Int.cast_natCast] using hmem')
  change v.asIdeal.ramificationIdx w.asIdeal = 1
  rw [hv]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p F w.asIdeal hpm

/-- The same genuine cyclotomic prime is unramified over the original ring of integers of Q; this follows through the actual prime localization, with no base-ring ramification formula assumed. -/
theorem rationalCyclotomic_originalBase_ramificationIdx_one
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} ℚ F]
    (w : HeightOneSpectrum (𝓞 F)) (hm : (m : 𝓞 F) ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
  letI : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain
      (R := ℤ) (p := w.asIdeal) w.ne_bot).mpr
      (rationalCyclotomic_ramificationIdx_one m w hm)
  letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal :=
    Algebra.FormallyUnramified.of_restrictScalars ℤ (𝓞 ℚ)
      (Localization.AtPrime w.asIdeal)
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt w.ne_bot

end
end Dubon2026
