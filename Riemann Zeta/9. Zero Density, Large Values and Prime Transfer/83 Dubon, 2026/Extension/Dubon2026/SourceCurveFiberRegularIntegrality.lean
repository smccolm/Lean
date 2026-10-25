import Dubon2026.SourceCurvePrimeNormOrders

/-! DUB-17/18 -> Weil reciprocity and Hecke adjointness -> norm evaluation
for functions regular on a fiber. The existing prime-order formula identifies
all denominator valuations with actual fiber orders. Dedekind factorization
then cancels the denominator, supplying the integral-closure element needed
by the proved residue norm formula. No global principal-divisor assumption
is needed. Adapted from S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain UniqueFactorizationMonoid
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem exists_integralClosureAt_of_fiber_ord_nonneg (v : Place K F) {f : E}
    (hord : ∀ w : Place K E, w.restrict F = v → 0 ≤ w.ord f) :
    ∃ c : integralClosureAt E v, algebraMap (integralClosureAt E v) E c = f := by
  classical
  by_cases hf : f = 0
  · exact ⟨0, by rw [map_zero, hf]⟩
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj (nonZeroDivisors (integralClosureAt E v)) f
  have hs : (s : integralClosureAt E v) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hsE : algebraMap (integralClosureAt E v) E (s : integralClosureAt E v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt E v) E)).mpr hs
  have hcE : algebraMap (integralClosureAt E v) E c ≠ 0 := by
    rw [← hcs]
    exact mul_ne_zero hf hsE
  have hc : c ≠ 0 := fun h => hcE (by rw [h, map_zero])
  have hdom (w : Place K E) (hw : w.restrict F = v) :
      w.ord (algebraMap (integralClosureAt E v) E (s : integralClosureAt E v)) ≤
        w.ord (algebraMap (integralClosureAt E v) E c) := by
    rw [← hcs, w.ord_mul hf hsE]
    exact le_add_of_nonneg_left (hord w hw)
  have hle : (Ideal.span {c} : Ideal (integralClosureAt E v)) ≤ Ideal.span {(s : integralClosureAt E v)} := by
    have hspanC : (Ideal.span {c} : Ideal (integralClosureAt E v)) ≠ ⊥ := by simpa using hc
    have hspanS : (Ideal.span {(s : integralClosureAt E v)} : Ideal (integralClosureAt E v)) ≠ ⊥ := by simp
    rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors hspanS hspanC,
      Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {(s : integralClosureAt E v)} : Ideal (integralClosureAt E v))
    · have hp := prime_of_normalized_factor P hP
      let Q : HeightOneSpectrum (integralClosureAt E v) := ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
      change (normalizedFactors (Ideal.span {(s : integralClosureAt E v)})).count Q.asIdeal ≤
        (normalizedFactors (Ideal.span {c})).count Q.asIdeal
      rw [fiberPrime_count_eq_order v Q hs, fiberPrime_count_eq_order v Q hc]
      exact Int.toNat_le_toNat (hdom _ (restrict_fiberPrimePlace v Q))
    · rw [Multiset.count_eq_zero_of_notMem hP]
      exact Nat.zero_le _
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self c))
  refine ⟨d, ?_⟩
  have hm := congrArg (algebraMap (integralClosureAt E v) E) hd
  rw [map_mul] at hm
  apply mul_left_cancel₀ hsE
  rw [← hm, ← hcs]
  exact mul_comm _ _

end
end Dubon2026.SourceCurve.Place
