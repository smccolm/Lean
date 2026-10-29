import Dubon2026.SourceToricAnalyticDivisionRoot
import Dubon2026.SourceEllipticExceptionalDivision

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> exact-order toric point. Reuse the native period lattice and
multiplication-polynomial formula to identify the abscissa of every
nonzero multiple. Its formal-series specialization will exclude smaller
torsion orders using the already proved coprimality of Phi and PsiSq. -/
namespace Dubon2026.SourceFunctionField.ToricAnalytic
noncomputable section
open WeierstrassCurve UpperHalfPlane SourceEllipticPeriod SourceEllipticExceptional

theorem toricPeriodHom_fraction_congr (τ : ℍ) (N : ℕ) [NeZero N]
    (a b : ℤ) (hab : (a : ZMod N) = (b : ZMod N)) :
    toricPeriodHom τ ((a : ℂ) / N) = toricPeriodHom τ ((b : ℂ) / N) := by
  rw [← sub_eq_zero, ← map_sub]
  change periodModelHom (PeriodLattice.ofTau τ) tateChange
    ((a : ℂ) / N - (b : ℂ) / N) = 0
  rw [← AddMonoidHom.mem_ker, ker_periodModelHom]
  change (a : ℂ) / N - (b : ℂ) / N ∈ (PeriodLattice.ofTau τ).lattice
  have he : (a : ℂ) / N - (b : ℂ) / N =
      ((0 : ℤ) * (τ : ℂ) + ((a - b : ℤ) : ℂ)) / N := by
    push_cast
    ring
  rw [he, fraction_mem_period_lattice_iff]
  refine ⟨dvd_zero _, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) N).mp
  simp only [Int.cast_sub, hab, sub_self]

theorem toricPeriodHom_fraction_mul (τ : ℍ) (N : ℕ) [NeZero N]
    (c : ZMod N) (m : ℕ) :
    m • toricPeriodHom τ ((c.val : ℂ) / N) =
      toricPeriodHom τ ((((m : ZMod N) * c).val : ℂ) / N) := by
  rw [← map_nsmul]
  have he : m • ((c.val : ℂ) / N) = (((m : ℤ) * c.val : ℤ) : ℂ) / N := by
    simp only [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_div_assoc]
  rw [he]
  exact toricPeriodHom_fraction_congr τ N ((m : ℤ) * c.val) ((m : ZMod N) * c).val
    (by simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val])

theorem tateCurve_divisionForm_mul_eval (τ : ℍ) (N : ℕ) [NeZero N]
    (c : ZMod N) (hc : c ≠ 0) (m : ℕ) (hmc : (m : ZMod N) * c ≠ 0) :
    (GammaOne.divisionForm N ((m : ZMod N) * c) hmc τ - 1 / 12) *
      ((tateCurve τ).ΨSq m).eval (GammaOne.divisionForm N c hc τ - 1 / 12) =
        ((tateCurve τ).Φ m).eval (GammaOne.divisionForm N c hc τ - 1 / 12) := by
  classical
  obtain ⟨y, h, he⟩ := toricPeriodHom_fraction_eq_some τ N c hc
  obtain ⟨y', h', he'⟩ := toricPeriodHom_fraction_eq_some τ N _ hmc
  have hm := toricPeriodHom_fraction_mul τ N c m
  rw [he, he'] at hm
  have hne : m • Affine.Point.some _ y h ≠ 0 := by
    rw [hm]
    exact Affine.Point.some_ne_zero h'
  obtain ⟨hΨ, hx⟩ := nsmul_xco_eq_div (tateCurve τ) m h hne
  rw [natCast_zsmul, hm, xco_some] at hx
  exact (eq_div_iff hΨ).mp (Option.some.inj hx)

end
end Dubon2026.SourceFunctionField.ToricAnalytic
