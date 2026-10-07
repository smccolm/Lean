import Dubon2026.LatticeCuspHolomorphic

/-! # The true Petersson residue of the integrated lattice continuation -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The literal completed lattice integral against the actual cusp Petersson density. -/
def rectangularLatticeCuspCompleted {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) : ℂ :=
  ∫ z : ℍ in gamma0FundamentalDomain Q,
    latticeCompletedMellin (rectangularLatticePoint a b ha hb z) s * petersson k f f z

/-- The literal integrated lattice continuation is holomorphic away from its two possible poles. -/
theorem differentiableAt_rectangularLatticeCuspCompleted {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (rectangularLatticeCuspCompleted f a b ha hb) s := by
  have he : rectangularLatticeCuspCompleted f a b ha hb =
      (fun s : ℂ => rectangularLatticeCuspRegular f a b ha hb s - (1 / (2 * s)) * cuspPetersson f f +
        (1 / (2 * (s - 1))) * cuspPetersson f f) :=
    funext (rectangular_lattice_cusp_integral_eq_regular f a b ha hb)
  rw [he]
  have hA : DifferentiableAt ℂ (fun t : ℂ => 1 / (2 * t)) s := by
    apply (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.const_mul 2)
    exact mul_ne_zero (by norm_num) hs0
  have hB : DifferentiableAt ℂ (fun t : ℂ => 1 / (2 * (t - 1))) s := by
    apply (differentiableAt_const (1 : ℂ)).div ((differentiableAt_id.sub_const 1).const_mul 2)
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs1)
  exact ((differentiable_rectangularLatticeCuspRegular f a b ha hb s).sub
    (hA.mul_const _)).add (hB.mul_const _)

/-- The pole coefficient of the actual lattice-cusp integral is exactly one half the genuine Petersson pairing. -/
theorem rectangularLatticeCuspCompleted_residue_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun s : ℂ => (s - 1) * rectangularLatticeCuspCompleted f a b ha hb s)
      (𝓝[≠] 1) (𝓝 (cuspPetersson f f / 2)) := by
  let H : ℂ → ℂ := fun s =>
    (s - 1) * rectangularLatticeCuspRegular f a b ha hb s -
      ((s - 1) * (1 / (2 * s))) * cuspPetersson f f + cuspPetersson f f / 2
  have hR := (differentiable_rectangularLatticeCuspRegular f a b ha hb (1 : ℂ)).continuousAt
  have hH : ContinuousAt H (1 : ℂ) := by
    dsimp [H]
    fun_prop (disch := norm_num)
  have ht : Tendsto H (𝓝[≠] (1 : ℂ)) (𝓝 (cuspPetersson f f / 2)) := by
    have h : Tendsto H (𝓝[≠] (1 : ℂ)) (𝓝 (H 1)) := hH.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [H, sub_self, zero_mul, sub_zero, zero_add] using h
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ (1 : ℂ) := hs
  have hc : (s - 1) * (1 / (2 * (s - 1))) = (1 / 2 : ℂ) := by
    field_simp [sub_ne_zero.mpr hs1]
  rw [rectangularLatticeCuspCompleted, rectangular_lattice_cusp_integral_eq_regular]
  dsimp [H]
  linear_combination -hc * cuspPetersson f f

end
end Dubon2026
