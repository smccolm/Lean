import Dubon2026.SourceEllipticPeriodCurve

/-! The actual analytic map to the nonsingular points of the period curve.
This supplies the map whose surjectivity and addition law are needed for the
odd-prime modular-polynomial product and DUB-17/18 cyclic-root interpretation.
Ellipticity is an explicit curve hypothesis, already proved for ofTau pairs.
Adapted from the frozen Apache-2.0 FLT period uniformization definition. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve
open scoped PeriodPair
noncomputable section
variable (L : PeriodPair) [(periodCurve L).IsElliptic]

/-- The actual Weierstrass functions give a point, with the lattice sent to infinity. -/
def periodPoint (z : ℂ) : (periodCurve L).toAffine.Point := by
  classical
  exact if hz : z ∈ L.lattice then 0 else
    .some _ _ ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      (periodCurve L).isUnit_Δ.ne_zero).mp (periodCurve_equation L hz))

theorem periodPoint_of_mem {z : ℂ} (hz : z ∈ L.lattice) : periodPoint L z = 0 := by
  simp [periodPoint, hz]

theorem periodPoint_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    periodPoint L z = .some _ _
      ((WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
        (periodCurve L).isUnit_Δ.ne_zero).mp (periodCurve_equation L hz)) := by
  simp [periodPoint, hz]

theorem periodPoint_zero : periodPoint L 0 = 0 := periodPoint_of_mem L (zero_mem _)

theorem periodPoint_eq_zero_iff (z : ℂ) : periodPoint L z = 0 ↔ z ∈ L.lattice := by
  refine ⟨fun hz => by_contra fun hnz => ?_, periodPoint_of_mem L⟩
  rw [periodPoint_of_notMem L hnz] at hz
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ hz

theorem periodPoint_add_mem (z : ℂ) {l : ℂ} (hl : l ∈ L.lattice) :
    periodPoint L (z + l) = periodPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [periodPoint_of_mem L hz, periodPoint_of_mem L (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun hmem => hz (by simpa using sub_mem hmem hl)
    rw [periodPoint_of_notMem L hz, periodPoint_of_notMem L hzl]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨L.weierstrassP_add_coe z ⟨l, hl⟩,
      by rw [L.derivWeierstrassP_add_coe z ⟨l, hl⟩]⟩

theorem periodPoint_neg (z : ℂ) : periodPoint L (-z) = -periodPoint L z := by
  by_cases hz : z ∈ L.lattice
  · rw [periodPoint_of_mem L hz, periodPoint_of_mem L (neg_mem hz)]
    rfl
  · have hnz : -z ∉ L.lattice := fun hmem => hz (by simpa using neg_mem hmem)
    rw [periodPoint_of_notMem L hz, periodPoint_of_notMem L hnz,
      WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨L.weierstrassP_neg z, ?_⟩
    rw [L.derivWeierstrassP_neg]
    change -℘'[L] z / 2 = -(℘'[L] z / 2) - 0 * ℘[L] z - 0
    ring

end
end Dubon2026.SourceEllipticPeriod
