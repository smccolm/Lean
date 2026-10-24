import Dubon2026.SourceEllipticPeriodPoint
import Dubon2026.SourceEllipticWeierstrassSurjectivity

/-! Every actual nonsingular point of an elliptic period curve is reached by
the Weierstrass functions. Surjectivity of x and the two y-solutions give the
claim, using z and -z. Together with SourceEllipticPeriodPointAddition,
this supplies the uniformization required by the odd-prime product identity
on the DUB-17/18 dependency chain.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean. -/

namespace Dubon2026.SourceEllipticPeriod
open scoped PeriodPair

theorem periodPoint_surjective (L : PeriodPair) [(periodCurve L).IsElliptic] :
    Function.Surjective (periodPoint L) := by
  intro P
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨0, periodPoint_zero L⟩
  obtain ⟨z, hz, hx⟩ := weierstrassP_surjective L x
  have hsq : (℘'[L] z / 2) ^ 2 = y ^ 2 := by
    have h1 := periodCurve_equation L hz
    have h2 := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
    simp only [periodCurve, hx, zero_mul, add_zero] at h1 h2
    linear_combination h1 - h2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy
  · refine ⟨z, ?_⟩
    rw [periodPoint_of_notMem L hz]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · have hnz : -z ∉ L.lattice := fun hm => hz (neg_neg z ▸ neg_mem hm)
    refine ⟨-z, ?_⟩
    rw [periodPoint_of_notMem L hnz]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨(L.weierstrassP_neg z).trans hx, ?_⟩
    rw [L.derivWeierstrassP_neg]
    linear_combination -hy

end Dubon2026.SourceEllipticPeriod
