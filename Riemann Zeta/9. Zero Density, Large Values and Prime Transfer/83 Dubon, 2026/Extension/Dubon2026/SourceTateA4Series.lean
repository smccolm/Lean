import Dubon2026.SourceModularJSeries

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. The literal integral Tate a4 series
and its relation to the already defined integer E4 series are needed to
identify the weight-four toric invariant. Only this required coefficient
series is introduced here. Adapted from the Apache-2.0 Anthropic FLT
TateFormal definition and ToricFourier proof, pinned at
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

/-- The literal integral Tate a4 series, with coefficients minus five times the cubic divisor sum. -/
def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

theorem coeff_tateA4 (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) :=
  PowerSeries.coeff_mk n _

namespace GammaOne.ToricFourier
theorem eisenstein4_map_eq (F : Type*) [Field F] :
    eisenstein4.map (Int.castRingHom F) = 1 - 48 * tateA4.map (Int.castRingHom F) := by
  rw [show (48 : PowerSeries F) = PowerSeries.C (48 : F) from (map_ofNat _ 48).symm]
  ext n
  rw [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, coeff_tateA4, eisenstein4, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, if_false, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast, Int.cast_neg, zero_sub, Finset.mul_sum, mul_neg, neg_neg]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

end GammaOne.ToricFourier
end
end Dubon2026.SourceFunctionField
