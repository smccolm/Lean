import GafniTao.PintzZetaAFEFiniteHead

/-!
# Exact hybrid single-zeta approximate functional equation

The two completed-zeta right edges are rewritten as vertical-truncation
series.  A finite set of positive coefficients on each edge is then displaced
to the left.  The resulting hybrid expression converges to the actual
`riemannZeta`; both complement series remain literal, so this theorem does not
presuppose their eventual estimates.
-/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace GafniTao

noncomputable section

/-- The opened right-edge series agrees exactly with the termwise normalized
vertical-truncation series. -/
theorem pintzZetaAFERightSeries_eq_verticalTrunc
    (s base : ℂ) (c H : ℝ) :
    (1 / (2 * Real.pi : ℂ)) *
        ∑' n : ℕ, (∫ u in -H..H,
          pintzZetaAFERightTerm s base c u n) =
      ∑' n : ℕ, pintzZetaAFETermVerticalTrunc s base n c H := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  exact (pintzZetaAFETermVerticalTrunc_eq_rightTerm s base n c H).symm

/-- The exact finite residue head selected on one side of the functional
equation. -/
noncomputable def pintzZetaAFEHeadResidue
    (s base : ℂ) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, pintzZetaAFETermNumerator s base n 0

/-- One hybrid edge: selected coefficients on the left line and the literal
complement on the original right line. -/
noncomputable def pintzZetaAFEHybridEdge
    (s base : ℂ) (S : Finset ℕ) (q c H : ℝ) : ℂ :=
  (∑ n ∈ S, pintzZetaAFETermVerticalTrunc s base n (-q) H) +
    ∑' n : {n : ℕ // n ∉ S},
      pintzZetaAFETermVerticalTrunc s base n.1 c H

/-- The two functional-equation edges together with both exact finite residue
heads. -/
noncomputable def pintzZetaAFEHybridApprox
    (s : ℂ) (S₁ S₂ : Finset ℕ) (q c H : ℝ) : ℂ :=
  pintzZetaAFEHeadResidue s s S₁ +
    pintzZetaAFEHeadResidue s (1 - s) S₂ +
    pintzZetaAFEHybridEdge s s S₁ q c H +
    pintzZetaAFEHybridEdge s (1 - s) S₂ q c H

/-- Exact two-sided finite-head AFE.  Under the source strip hypotheses the
hybrid expression converges to the genuine zeta value. -/
theorem tendsto_pintzZetaAFEHybridApprox
    (s : ℂ) (S₁ S₂ : Finset ℕ)
    (hS₁ : ∀ n ∈ S₁, n ≠ 0) (hS₂ : ∀ n ∈ S₂, n ≠ 0)
    {q c : ℝ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hq : 0 < q) (hc : 0 < c)
    (hqs : q < s.re) (hq1s : q < (1 - s).re)
    (hright₁ : 1 < s.re + c) (hright₂ : 1 < (1 - s).re + c) :
    Tendsto (fun H : ℝ => pintzZetaAFEHybridApprox s S₁ S₂ q c H)
      atTop (nhds (riemannZeta s)) := by
  have hfull : Tendsto (fun H : ℝ =>
      (∑' n : ℕ, pintzZetaAFETermVerticalTrunc s s n c H) +
        ∑' n : ℕ, pintzZetaAFETermVerticalTrunc s (1 - s) n c H)
      atTop (nhds (riemannZeta s)) := by
    have h := tendsto_pintzZetaAFERightSeries s hs0 hs1 hright₁ hright₂
    apply h.congr'
    filter_upwards with H
    rw [pintzZetaAFERightSeries_eq_verticalTrunc,
      pintzZetaAFERightSeries_eq_verticalTrunc]
  have hdisp₁ := tendsto_pintzZetaAFERightSeries_displaced_finset
    s s S₁ hS₁ hq hc hqs hright₁
  have hdisp₂ := tendsto_pintzZetaAFERightSeries_displaced_finset
    s (1 - s) S₂ hS₂ hq hc hq1s hright₂
  have hdiff : Tendsto (fun H : ℝ =>
      ((∑' n : ℕ, pintzZetaAFETermVerticalTrunc s s n c H) -
          pintzZetaAFEHybridEdge s s S₁ q c H) +
        ((∑' n : ℕ, pintzZetaAFETermVerticalTrunc s (1 - s) n c H) -
          pintzZetaAFEHybridEdge s (1 - s) S₂ q c H))
      atTop (nhds (pintzZetaAFEHeadResidue s s S₁ +
        pintzZetaAFEHeadResidue s (1 - s) S₂)) := by
    simpa only [pintzZetaAFEHybridEdge, pintzZetaAFEHeadResidue] using
      hdisp₁.add hdisp₂
  have hsub := hfull.sub hdiff
  have hadd := (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => pintzZetaAFEHeadResidue s s S₁ +
        pintzZetaAFEHeadResidue s (1 - s) S₂) atTop
      (nhds (pintzZetaAFEHeadResidue s s S₁ +
        pintzZetaAFEHeadResidue s (1 - s) S₂))).add hsub
  have hadd' : Tendsto (fun H : ℝ =>
      (pintzZetaAFEHeadResidue s s S₁ +
          pintzZetaAFEHeadResidue s (1 - s) S₂) +
        (((∑' n : ℕ, pintzZetaAFETermVerticalTrunc s s n c H) +
            ∑' n : ℕ, pintzZetaAFETermVerticalTrunc s (1 - s) n c H) -
          (((∑' n : ℕ, pintzZetaAFETermVerticalTrunc s s n c H) -
              pintzZetaAFEHybridEdge s s S₁ q c H) +
            ((∑' n : ℕ, pintzZetaAFETermVerticalTrunc s (1 - s) n c H) -
              pintzZetaAFEHybridEdge s (1 - s) S₂ q c H))))
      atTop (nhds (riemannZeta s)) := by
    convert hadd using 1
    ring_nf
  apply hadd'.congr'
  filter_upwards with H
  unfold pintzZetaAFEHybridApprox
  ring_nf

#print axioms pintzZetaAFERightSeries_eq_verticalTrunc
#print axioms tendsto_pintzZetaAFEHybridApprox

end

end GafniTao
