import Dubon2026.UnramifiedIntegralValuations

/-! # Ramification in the original finite-place valuations

The exact power formula is needed to extend the actual base-field embedding
to the original adic completions. That embedding is the first comparison
needed to identify the original invariant idele-class norm quotient with
the base-field norm quotient, in DUB-17's global duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped WithZero

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]

/-- The original integral valuation restricts by the actual ramification index. -/
theorem original_intValuation_algebraMap_pow
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (r : R) :
    w.intValuation (algebraMap R S r) =
      v.intValuation r ^ v.asIdeal.ramificationIdx w.asIdeal := by
  classical
  have he : v.asIdeal.ramificationIdx w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver w.asIdeal v.ne_bot
  by_cases hr : r = 0
  · simp only [hr, map_zero, zero_pow he]
  have hmap : algebraMap R S r ≠ 0 := by
    intro hz
    apply hr
    apply FaithfulSMul.algebraMap_injective R S
    simpa only [map_zero] using hz
  have hI : (Ideal.span {r} : Ideal R) ≠ ⊥ :=
    Submodule.span_singleton_eq_bot.mp.mt hr
  have hm := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
    hI v.irreducible w.irreducible w.ne_bot
  have hm' : multiplicity w.asIdeal (Ideal.span {algebraMap R S r}) =
      v.asIdeal.ramificationIdx w.asIdeal * multiplicity v.asIdeal (Ideal.span {r}) := by
    apply multiplicity_eq_of_emultiplicity_eq_some
    rw [Ideal.map_span, Set.image_singleton] at hm
    rw [hm, (FiniteMultiplicity.of_prime_left v.prime hI).emultiplicity_eq_multiplicity]
    exact (Nat.cast_mul _ _).symm
  rw [w.intValuation_eq_exp_neg_multiplicity hmap,
    v.intValuation_eq_exp_neg_multiplicity hr, hm']
  rw [← WithZero.exp_nsmul]
  congr 1
  simp only [Nat.cast_mul, nsmul_eq_mul, mul_neg]

end
end Dubon2026
