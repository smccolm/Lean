import Dubon2026.SourceEllipticPeriodUniformization

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> faithful Fricke generators.
Reuse the existing actual period homomorphism and its exact lattice kernel,
together with the native elliptic-point x-coordinate theorem. This avoids
a new low-Fourier-coefficient case analysis and assumes no separation result. -/
namespace Dubon2026.SourceFricke
noncomputable section
open SourceEllipticPeriod
open scoped PeriodPair

theorem weierstrassP_eq_imp_lattice (L : PeriodPair) [(periodCurve L).IsElliptic]
    {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z = ℘[L] w) :
    z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  have hx : (periodPoint L z).xRep = (periodPoint L w).xRep := by
    rw [periodPoint_of_notMem L hz, periodPoint_of_notMem L hw]
    simp only [WeierstrassCurve.Affine.Point.xRep_some, h]
  rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hx with hp | hp
  · left
    apply (periodPoint_eq_zero_iff L (z - w)).mp
    change periodHom L (z - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hp
  · right
    apply (periodPoint_eq_zero_iff L (z + w)).mp
    change periodHom L (z + w) = 0
    rw [map_add]
    exact eq_neg_iff_add_eq_zero.mp hp

end
end Dubon2026.SourceFricke
