import Dubon2026.SourceOriginalWeilRestrictionCovering
import Dubon2026.SourceOriginalWeilCoverEvaluationContinuity
import Dubon2026.SourceOriginalAnalyticCellCoordinates
import Dubon2026.SourceOriginalComplexChartOrders

/-! DUB-17/18 -> cover reciprocity -> analytic lifted cells.
A coordinate obtained by lifting an original analytic cell has holomorphic
nonsingular transitions to the actual cover charts. This is proved from the
literal restriction comparison, rather than assumed as a sheet property. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
attribute [local instance] restrictionIntegral

theorem analytic_lifted_coordinate (A : CellGeometry.AnalyticCoord N) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    letI := OriginalChart.placeTopology N
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ w ∈ ζ.source, w.restrict FF ∈ A.ζ.source ∧ ζ w = A.ζ (w.restrict FF)) →
      ∀ w ∈ ζ.source,
        AnalyticAt ℂ (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders w) 0 ∧
          deriv (ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders w) 0 ≠ 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := OriginalChart.placeTopology N
  letI := OriginalChart.placeChartedSpace N
  intro ζ hζ w hw
  let b := A.ζ ∘ OriginalChart.placeFamily N (w.restrict FF)
  have hb : AnalyticAt ℂ b 0 := by
    simpa only [OriginalChart.extPlaceChart_self, Function.comp_def,
      OriginalChart.extPlaceChart_symm_apply] using A.analytic (w.restrict FF) (hζ w hw).1
  have hbd : deriv b 0 ≠ 0 := by
    simpa only [OriginalChart.extPlaceChart_self, Function.comp_def,
      OriginalChart.extPlaceChart_symm_apply] using A.deriv_ne (w.restrict FF) (hζ w hw).1
  let g := (restrictionComparison N n radicand baseDivisor hRadicand hOrders w).transition
  obtain ⟨hg, hgd, hg0, hcomp⟩ :=
    restriction_chart_comparison N n radicand baseDivisor hRadicand hOrders w
  change AnalyticAt ℂ g 0 at hg
  change deriv g 0 ≠ 0 at hgd
  change g 0 = 0 at hg0
  have hnear : ∀ᶠ z in 𝓝 (0 : ℂ),
      placeFamily N n radicand baseDivisor hRadicand hOrders w z ∈ ζ.source := by
    have hc := placeFamily_continuousAt_zero N n radicand baseDivisor hRadicand hOrders w
    apply hc.eventually
    simpa only [(place_spec N n radicand baseDivisor hRadicand hOrders w).2.1] using
      ζ.open_source.mem_nhds hw
  have heq : ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders w =ᶠ[𝓝 0] b ∘ g := by
    filter_upwards [hnear, hcomp] with z hz he
    exact (hζ _ hz).2.trans (congrArg A.ζ he)
  have hbg : AnalyticAt ℂ b (g 0) := by rw [hg0]; exact hb
  have hd := hbg.hasStrictDerivAt.hasDerivAt.comp 0 hg.hasStrictDerivAt.hasDerivAt
  have hn : deriv b (g 0) * deriv g 0 ≠ 0 := by rw [hg0]; exact mul_ne_zero hbd hgd
  exact ⟨(hbg.comp hg).congr heq.symm,
    by rw [heq.deriv_eq, hd.deriv]; exact hn⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
