import Dubon2026.SourceOriginalTwoPrimeGeneration

/-! DUB-17/18 -> numerical modular genus -> mixed prime-power field
decomposition. If two distinct primes divide d, the two immediate
divisor series j_(d/p) and j_(d/q) generate j_d inside any actual rational
Laurent subfield containing them. Native coprime divisibility reduces
this to the proved literal two-prime relation intersection.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem original_divisor_series_mem_of_two_primes (d p q : ℕ) [NeZero d]
    [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hpd : p ∣ d) (hqd : q ∣ d) [NeZero (d / p)] [NeZero (d / q)]
    (F : IntermediateField ℚ (LaurentSeries ℚ))
    (h1 : qExpand ℚ (d / p) jq ∈ F) (h2 : qExpand ℚ (d / q) jq ∈ F) :
    qExpand ℚ d jq ∈ F := by
  obtain ⟨m, hm⟩ := ((Nat.coprime_primes hp.out hq.out).mpr hpq).mul_dvd_of_dvd_of_dvd hpd hqd
  haveI : NeZero m := ⟨fun he => NeZero.ne d (by rw [hm, he, mul_zero])⟩
  have hd : d = m * p * q := by rw [hm]; ring
  have hdivp : d / p = m * q := by
    calc
      d / p = (p * (m * q)) / p := by congr 1; rw [hd]; ring
      _ = m * q := Nat.mul_div_cancel_left _ hp.out.pos
  have hdivq : d / q = m * p := by rw [hd, Nat.mul_div_cancel _ hq.out.pos]
  rw [qExpand_congr hdivp jq] at h1
  rw [qExpand_congr hdivq jq] at h2
  rw [qExpand_congr hd jq]
  exact original_two_prime_generation m p q hpq F h2 h1

end
end Dubon2026.SourceFunctionField
