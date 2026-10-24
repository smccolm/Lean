import Dubon2026.SourceJointChartMonomialFactors
import Dubon2026.LocalMonicSeparableReduction

/-! DUB-17/18 -> Kummer power lifting -> finite overlap -> two-chart
decomposition. A good constant-reduction factor is coprime to every monic
polynomial over the coefficient valuation ring. The existing resultant-map
theorem lifts residue coprimality and supplies integral Bezout coefficients. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

theorem isCoprime_of_monic_and_good
    {L : Type} [Field L] (A : ValuationSubring L)
    (a b : A[X]) (ha : a.Monic) (hb : IsGood A (b.map A.subtype)) : IsCoprime a b := by
  have hmap : b.map (residue A) = C (residue A (b.coeff 0)) := by
    ext n
    rw [coeff_map, coeff_C]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      apply (residue_eq_zero_iff _).mpr
      apply (A.valuation_lt_one_iff _).mpr
      simpa only [coeff_map] using hb.2 n hn
  have hb0 : IsUnit (b.coeff 0) := (A.valuation_eq_one_iff _).mpr
    (by simpa only [coeff_map] using hb.1)
  apply (Polynomial.isUnit_resultant_iff_isCoprime ha).mp
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [← Dubon2026.monic_resultant_map (residue A) a b ha]
  apply IsUnit.ne_zero
  apply (Polynomial.isUnit_resultant_iff_isCoprime (ha.map (residue A))).mpr
  rw [hmap]
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mp ((hb0.map (residue A)).map C)
  exact ⟨0, c, by simpa only [zero_mul, zero_add] using hc⟩

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
