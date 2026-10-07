import Dubon2026.LatticeCuspContinuationIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Holomorphy under the actual regularized lattice-cusp integral -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter Metric
open scoped Topology

noncomputable section

/-- The actual spectral derivative of the regularized lattice kernel is spatially measurable. -/
theorem measurable_deriv_latticeCompletedMellinRegular (s : ℂ) :
    Measurable (fun z : ℍ => deriv (latticeCompletedMellinRegular z) s) := by
  apply measurable_of_tendsto_metrizable' (𝓝[≠] s)
    (f := fun t : ℂ => fun z : ℍ => slope (latticeCompletedMellinRegular z) s t)
  · intro t
    exact ((measurable_latticeCompletedMellinRegular t).sub
      (measurable_latticeCompletedMellinRegular s)).const_smul (t - s)⁻¹
  · rw [tendsto_pi_nhds]
    intro z
    exact (differentiable_latticeCompletedMellinRegular z s).hasDerivAt.tendsto_slope

/-- Cauchy's inequality gives a genuine spectral derivative majorant by a convergent positive lattice value. -/
theorem norm_deriv_latticeCompletedMellinRegular_le (z : ℍ) {s : ℂ} {σ : ℝ}
    (hσ : 1 < σ) (hs : s.re + 1 ≤ σ) (hs' : 2 - s.re ≤ σ) :
    ‖deriv (latticeCompletedMellinRegular z) s‖ ≤ 2 * (latticeCompletedMellin z (σ : ℂ)).re := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1)
    (C := 2 * (latticeCompletedMellin z (σ : ℂ)).re) (by norm_num)
    (differentiable_latticeCompletedMellinRegular z).diffContOnCl
  simp only [div_one] at h
  apply h
  intro w hw
  have hn : ‖w - s‖ = 1 := by simpa only [mem_sphere, dist_eq_norm] using hw
  have hr := Complex.abs_re_le_norm (w - s)
  rw [hn, Complex.sub_re] at hr
  have hrl := (abs_le.mp hr).1
  have hru := (abs_le.mp hr).2
  exact norm_latticeCompletedMellinRegular_le z hσ (by linarith) (by linarith)

/-- Differentiation under the literal lattice-cusp integral is justified by the proved integrable cusp majorant. -/
theorem hasDerivAt_rectangularLatticeCuspRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    HasDerivAt (rectangularLatticeCuspRegular f a b ha hb)
      (∫ z : ℍ in gamma0FundamentalDomain Q,
        deriv (latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z)) s * petersson k f f z) s := by
  let σ : ℝ := |s.re| + 4
  have hσ : 1 < σ := by dsimp [σ]; linarith [abs_nonneg s.re]
  have hm (t : ℂ) := ((measurable_deriv_latticeCompletedMellinRegular t).comp
    (continuous_rectangularLatticePoint a b ha hb).measurable).mul
      (petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f)).measurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t z => latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z) t * petersson k f f z)
    (F' := fun t z => deriv (latticeCompletedMellinRegular (rectangularLatticePoint a b ha hb z)) t * petersson k f f z)
    (bound := fun z : ℍ => 2 * (‖latticeCompletedMellin (rectangularLatticePoint a b ha hb z) (σ : ℂ)‖ *
      ‖petersson k f f z‖))
    (ball_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun t => (integrableOn_rectangular_lattice_regular_petersson f a b ha hb t).aestronglyMeasurable))
    (integrableOn_rectangular_lattice_regular_petersson f a b ha hb s)
    (hm s).aestronglyMeasurable.restrict ?_
    ((integrableOn_norm_rectangular_lattice_petersson f a b ha hb hσ).const_mul 2) ?_).2
  · apply ae_of_all
    intro z t ht
    have hn : ‖t - s‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using ht
    have hr := Complex.abs_re_le_norm (t - s)
    have hl := (abs_lt.mp (lt_of_le_of_lt hr hn)).1
    have hu := (abs_lt.mp (lt_of_le_of_lt hr hn)).2
    simp only [Complex.sub_re] at hl hu
    have h1 : t.re + 1 ≤ σ := by dsimp [σ]; linarith [le_abs_self s.re]
    have h2 : 2 - t.re ≤ σ := by dsimp [σ]; linarith [neg_le_abs s.re]
    dsimp only
    rw [norm_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_deriv_latticeCompletedMellinRegular_le _ hσ h1 h2).trans
      (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num))
  · apply ae_of_all
    intro z t ht
    exact (differentiable_latticeCompletedMellinRegular
      (rectangularLatticePoint a b ha hb z) t).hasDerivAt.mul_const _

/-- The actual regularized lattice-cusp integral is entire, with no domination hypothesis supplied. -/
theorem differentiable_rectangularLatticeCuspRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Differentiable ℂ (rectangularLatticeCuspRegular f a b ha hb) :=
  fun s => (hasDerivAt_rectangularLatticeCuspRegular f a b ha hb s).differentiableAt

end
end Dubon2026
