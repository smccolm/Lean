import Dubon2026.FiniteAdelicLocalIntegral
import Dubon2026.RationalPrimePlace

/-! # Genuine local integer units from original rational-prime nondivisibility -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-- The original rational inverse of an integer away from the actual place remains in the genuine local integer ring. -/
theorem finitePlace_inverse_integer_integral (v : HeightOneSpectrum ℤ) (a : ℤ)
    (ha : a ∉ v.asIdeal) :
    algebraMap ℚ (v.adicCompletion ℚ) ((a : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_adicCompletionIntegers, algebraMap_adicCompletion, Function.comp_apply,
    Valued.valuedCompletion_apply]
  change v.valuation ℚ ((a : ℚ)⁻¹) ≤ 1
  have hv : v.valuation ℚ (a : ℚ) = 1 := by
    change v.valuation ℚ (algebraMap ℤ ℚ a) = 1
    rw [valuation_of_algebraMap]
    exact intValuation_eq_one_iff.mpr ha
  rw [map_inv₀, hv, inv_one]

/-- Every original integer outside the actual prime ideal is literally the value of a genuine local integral unit. -/
theorem finitePlace_integer_unit (v : HeightOneSpectrum ℤ) (a : ℤ) (ha : a ∉ v.asIdeal) :
    ∃ u : (v.adicCompletionIntegers ℚ)ˣ, (u.val : v.adicCompletion ℚ) = a := by
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (h ▸ v.asIdeal.zero_mem)
  have hq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha0
  let b : v.adicCompletionIntegers ℚ :=
    ⟨algebraMap ℚ (v.adicCompletion ℚ) ((a : ℚ)⁻¹), finitePlace_inverse_integer_integral v a ha⟩
  have hu : IsUnit (a : v.adicCompletionIntegers ℚ) := by
    apply IsUnit.of_mul_eq_one b
    apply Subtype.ext
    change (a : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) ((a : ℚ)⁻¹) = 1
    rw [← map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) a, ← map_mul, mul_inv_cancel₀ hq, map_one]
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, congrArg Subtype.val hu⟩

/-- Original integer divisibility exactly characterizes membership in the genuine rational-prime ideal. -/
theorem rationalPrimePlace_int_mem_iff (p : ℕ) (hp : p.Prime) (a : ℤ) :
    a ∈ (rationalPrimePlace p hp).asIdeal ↔ (p : ℤ) ∣ a := by
  have he : (p : ℤ) ∣ a ↔ a ∈ (rationalPrimePlace p hp).asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton,
      rationalPrimePlace_natGenerator]
  have heq : Rat.IsIntegralClosure.intEquiv ℤ a = a := by simp
  conv_rhs at he => rw [← heq, Ideal.apply_mem_of_equiv_iff]
  exact he.symm

/-- Nondivisibility by the original prime supplies an actual integral local unit with the exact original integer value. -/
theorem rationalPrimePlace_integer_unit (p : ℕ) (hp : p.Prime) (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    ∃ u : ((rationalPrimePlace p hp).adicCompletionIntegers ℚ)ˣ,
      (u.val : (rationalPrimePlace p hp).adicCompletion ℚ) = a := by
  apply finitePlace_integer_unit
  rwa [rationalPrimePlace_int_mem_iff]

end
end Dubon2026
