import Dubon2026.ArithmeticFaithfulFactorUnramified
import Dubon2026.UnramifiedUnionFiniteRamification

/-! Removing ramification at the selected auxiliary primes from the
actual extension supported on a times their product gives unramifiedness
outside the original support. Primality of each actual global prime
reduces the product support directly to one selected prime. This is the
finite-field containment criterion needed for Dubon Theorem 2.6's
base-support deformation quotient. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators

private theorem prime_liesOver_of_prime_mem
    {F : Type} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hp : p.Prime)
    (hmem : (p : 𝓞 F) ∈ w.asIdeal) :
    w.asIdeal.LiesOver (rationalOriginalPrimePlace p hp).asIdeal := by
  letI : w.asIdeal.IsPrime := w.isPrime
  have hle : (rationalOriginalPrimePlace p hp).asIdeal ≤ w.asIdeal.under (𝓞 ℚ) := by
    rw [rationalOriginalPrimePlace_eq_span, Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal
    simpa only [map_natCast] using hmem
  exact ⟨(rationalOriginalPrimePlace p hp).isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩

/-- An actual finite arithmetic field with product auxiliary support
and genuine unramifiedness at the selected primes is unramified at every
original prime outside the original support integer. -/
theorem rationalArithmetic_finite_field_original_support_ramification
    (a b : 𝓞 ℚ) (hb : b ≠ 0) (Q : Finset Nat.Primes)
    (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension b))
    (hQ : ∀ p : Q, Chebotarev.UnramifiedIn ℚ F (Ideal.span {(p.val.val : 𝓞 ℚ)}))
    (w : HeightOneSpectrum (𝓞 F))
    (hwa : algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : w.asIdeal.IsPrime := w.isPrime
  by_cases hwb : algebraMap (𝓞 ℚ) (𝓞 F) b ∈ w.asIdeal
  · have hmap : algebraMap (𝓞 ℚ) (𝓞 F) b = algebraMap (𝓞 ℚ) (𝓞 F) a *
        ∏ p ∈ Q, algebraMap (𝓞 ℚ) (𝓞 F) (p.val : 𝓞 ℚ) :=
      (congrArg (algebraMap (𝓞 ℚ) (𝓞 F)) hba).trans (by rw [map_mul, map_prod])
    rw [hmap] at hwb
    have hprod := (w.isPrime.mem_or_mem hwb).resolve_left hwa
    obtain ⟨p, hpQ, hpm⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
    have hpm' : (p.val : 𝓞 F) ∈ w.asIdeal := by simpa only [map_natCast] using hpm
    let v := rationalOriginalPrimePlace p.val p.property
    letI : w.asIdeal.LiesOver v.asIdeal := prime_liesOver_of_prime_mem w p.val p.property hpm'
    have hu : Chebotarev.UnramifiedIn ℚ F v.asIdeal := by
      simpa only [v, rationalOriginalPrimePlace_eq_span] using hQ ⟨p, hpQ⟩
    letI : Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := hu.2 w.asIdeal w.isMaximal inferInstance
    rw [← Ideal.over_def w.asIdeal v.asIdeal]
    exact (numberField_isUnramifiedAt_iff_ramificationIdx_one v w).mp inferInstance
  · exact originalUnramifiedUnion_finite_ramification b hb F.toIntermediateField w hwb

end
end Dubon2026
