import RiemannZeta.GuthMaynard.DFIEquation29

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

theorem probe_support
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {S : ℝ}
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k : ℕ) :
    Function.support (dfiEquation29BesselRecurrenceIterate k g) ⊆
      Set.Icc S (2 * S) := by
  induction k generalizing g with
  | zero => simpa using hSupport
  | succ k ih =>
      let Rg : ℝ → ℂ := dfiEquation29BesselShiftIterate 2 g
      have hRg : DFIVoronoiTestFunction Rg := hg.besselShiftIterate 2
      have hRgSupport : Function.support Rg ⊆ Set.Icc S (2 * S) := by
        intro x hx
        apply closure_minimal hSupport isClosed_Icc
        have hxR : x ∈ tsupport Rg := subset_tsupport Rg hx
        have hxL : x ∈ tsupport (dfiMellinLogOperator 1 (deriv g)) := by
          rw [show Rg = dfiMellinLogOperator 1 (deriv g) from
            hg.besselShift_two_eq] at hxR
          exact hxR
        exact tsupport_deriv_subset
          (tsupport_dfiMellinLogOperator_subset 1 (deriv g) hxL)
      simpa [dfiEquation29BesselRecurrenceIterate_succ, Rg] using
        ih hRg hRgSupport

end RiemannZeta.GuthMaynard
