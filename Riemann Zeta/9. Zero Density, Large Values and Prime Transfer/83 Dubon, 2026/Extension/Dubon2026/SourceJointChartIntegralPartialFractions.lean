import Dubon2026.SourceJointChartIntegralCoprimality

/-! DUB-17/18 -> Kummer power lifting -> finite overlap -> two-chart
decomposition. Integral Bezout coefficients and native monic division give
the partial-fraction numerator identity with a bounded remainder. Reflection
then gives a good inverse-coordinate denominator. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

theorem exists_integral_partial_fraction_numerators
    {L : Type} [Field L] (A : ValuationSubring L)
    (p a b : A[X]) (ha : a.Monic) (hb : IsGood A (b.map A.subtype)) :
    ∃ P r : A[X], r.natDegree ≤ a.natDegree ∧ p = P * a + r * b := by
  obtain ⟨c, e, hce⟩ := isCoprime_of_monic_and_good A a b ha hb
  refine ⟨p * c + ((p * e) /ₘ a) * b, (p * e) %ₘ a,
    natDegree_modByMonic_le _ ha, ?_⟩
  calc p = p * (c * a + e * b) := by rw [hce, mul_one]
    _ = (p * c) * a + (p * e) * b := by ring
    _ = _ := by
      conv_lhs => rw [← modByMonic_add_div (p * e) a]
      ring

theorem good_reflect_top {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L[X]} (ha : IsGoodAt A a.natDegree a) : IsGood A (reflect a.natDegree a) := by
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coeff_reflect, revAt_zero]
    exact ha.1
  · rw [coeff_reflect]
    apply ha.2
    intro he
    have := congrArg (revAt a.natDegree) he
    rw [revAt_invol, revAt_le le_rfl, Nat.sub_self] at this
    exact hj this

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
