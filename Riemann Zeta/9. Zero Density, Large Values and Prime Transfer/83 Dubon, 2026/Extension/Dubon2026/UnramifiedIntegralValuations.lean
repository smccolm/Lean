import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-! # Original integral valuations agree at actual primes of ramification index one -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]

/-- At an actual prime of ramification index one, the original integral valuation restricts to the original base-prime valuation. -/
theorem unramified_intValuation_algebraMap
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1) (r : R) :
    w.intValuation (algebraMap R S r) = v.intValuation r := by
  classical
  by_cases hr : r = 0
  · simp only [hr, map_zero]
  have hmap : algebraMap R S r ≠ 0 := by
    intro h
    apply hr
    apply FaithfulSMul.algebraMap_injective R S
    simpa only [map_zero] using h
  have hI : (Ideal.span {r} : Ideal R) ≠ ⊥ :=
    Submodule.span_singleton_eq_bot.mp.mt hr
  have hm := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hI v.irreducible w.irreducible w.ne_bot
  have hm' : emultiplicity w.asIdeal (Ideal.span {algebraMap R S r}) =
      emultiplicity v.asIdeal (Ideal.span {r}) := by
    simpa only [he, Nat.cast_one, one_mul, Ideal.map_span, Set.image_singleton] using hm
  rw [w.intValuation_eq_exp_neg_multiplicity hmap,
    v.intValuation_eq_exp_neg_multiplicity hr,
    multiplicity_eq_of_emultiplicity_eq hm']

end
end Dubon2026
