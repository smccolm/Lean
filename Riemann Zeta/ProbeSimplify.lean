import RiemannZeta.GuthMaynard.DFIEquation29

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_first_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiMellinLogOperator 1 (dfiVoronoiInvWeight g) = deriv g := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hzero : g =ᶠ[nhds (0 : ℝ)] 0 := by
      filter_upwards [Iio_mem_nhds hg.lower_pos] with y hy
      have hgy : g y = 0 := by
        by_contra hne
        exact (not_le_of_gt hy) (hg.support_subset hne).1
      simp [hgy]
    have hizero : dfiVoronoiInvWeight g =ᶠ[nhds (0 : ℝ)] 0 := by
      filter_upwards [hzero] with y hy
      simp [dfiVoronoiInvWeight, hy]
    have hdg : deriv g 0 = 0 := by
      simpa using Filter.EventuallyEq.deriv_eq hzero
    have hdi : deriv (dfiVoronoiInvWeight g) 0 = 0 := by
      simpa using Filter.EventuallyEq.deriv_eq hizero
    simp [dfiMellinLogOperator, dfiVoronoiInvWeight, hdg, hdi]
  · have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hinv0 := hasDerivAt_ofReal_cpow_const
      (x := x) hx (r := (-1 : ℂ)) (by norm_num)
    have hinv : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹)
        (-((x : ℂ) ^ 2)⁻¹) x := by
      convert hinv0 using 1
      · simp [Complex.cpow_neg_one]
      · rw [show (-1 : ℂ) - 1 = ((-2 : ℤ) : ℂ) by norm_num,
          Complex.cpow_intCast]
        norm_num [zpow_neg, hxC, pow_two]
        field_simp
    have hgderiv : HasDerivAt g (deriv g x) x :=
      (hg.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    have hprod := hinv.mul hgderiv
    unfold dfiMellinLogOperator dfiVoronoiInvWeight
    rw [show deriv (fun y : ℝ => (y : ℂ)⁻¹ * g y) x =
        -((x : ℂ) ^ 2)⁻¹ * g x + (x : ℂ)⁻¹ * deriv g x from hprod.deriv]
    field_simp
    norm_num

theorem probe_second_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiEquation29BesselShiftIterate 2 g =
      dfiMellinLogOperator 1 (deriv g) := by
  rw [show dfiEquation29BesselShiftIterate 2 g =
      dfiMellinLogOperator 1
        (dfiMellinLogOperator 1 (dfiVoronoiInvWeight g)) by rfl]
  rw [probe_first_shift hg]

theorem probe_second_shift_apply
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (x : ℝ) :
    dfiEquation29BesselShiftIterate 2 g x =
      deriv g x + (x : ℂ) * deriv (deriv g) x := by
  rw [congrFun (probe_second_shift hg) x]
  simp [dfiMellinLogOperator]

theorem probe_iteratedDeriv_deriv
    {g : ℝ → ℂ} (j : ℕ) :
    iteratedDeriv j (deriv g) = iteratedDeriv (j + 1) g := by
  induction j with
  | zero => simp [iteratedDeriv_one]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      rw [← iteratedDeriv_succ]

theorem probe_second_shift_iterated
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x =
      ((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
        (x : ℂ) * iteratedDeriv (j + 2) g x := by
  rw [probe_second_shift hg]
  rw [iteratedDeriv_dfiMellinLogOperator
    (show ContDiff ℝ ∞ (deriv g) by
      simpa [iteratedDeriv_one] using
        (ContDiff.contDiff_iteratedDeriv_top hg.smooth 1)) j x]
  rw [congrFun (probe_iteratedDeriv_deriv (g := g) j) x]
  rw [congrFun (probe_iteratedDeriv_deriv (g := g) (j + 1)) x]
  congr 2

end RiemannZeta.GuthMaynard
