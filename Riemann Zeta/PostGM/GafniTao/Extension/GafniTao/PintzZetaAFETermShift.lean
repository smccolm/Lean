import GafniTao.PintzZetaAFETermHorizontalIntegral

/-!
# Infinite-height termwise displacement for the zeta AFE

This module passes the exact one-coefficient rectangle identity to infinite
height.  At this stage the conclusion is deliberately the difference of the
two truncated vertical integrals; no existence or size assertion for either
individual improper integral is smuggled into the statement.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The normalized vertical integral of one coefficient, truncated at height
`H`. -/
noncomputable def pintzZetaAFETermVerticalTrunc
    (s base : ℂ) (n : ℕ) (r H : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ u in (-H)..H,
      pintzZetaAFETermContourIntegrand s base n
        ((r : ℂ) + (u : ℂ) * I))

/-- Expansion of the normalized rectangle into the two horizontal and two
vertical sides, with the orientation used by the source contour shift. -/
theorem pintzZetaAFETerm_RectangleIntegral'_eq_edges
    (s base : ℂ) (n : ℕ) (q c H : ℝ) :
    RectangleIntegral' (pintzZetaAFETermContourIntegrand s base n)
        ((-q : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H) -
        HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c H +
        pintzZetaAFETermVerticalTrunc s base n c H -
        pintzZetaAFETermVerticalTrunc s base n (-q) H := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
    pintzZetaAFETermVerticalTrunc
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Infinite-height consequence of the termwise rectangle theorem.  The
difference between the right and left vertical truncations converges to the
exact residue of that positive Dirichlet coefficient. -/
theorem tendsto_pintzZetaAFETerm_vertical_difference
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ =>
      pintzZetaAFETermVerticalTrunc s base n c H -
        pintzZetaAFETermVerticalTrunc s base n (-q) H)
      atTop (nhds (pintzZetaAFETermNumerator s base n 0)) := by
  have hneg :=
    tendsto_pintzZetaAFETerm_HIntegral'_neg_zero s base hn hq hc hbase
  have hpos :=
    tendsto_pintzZetaAFETerm_HIntegral'_zero s base hn hq hc hbase
  have hlimit : Tendsto (fun H : ℝ =>
      pintzZetaAFETermNumerator s base n 0 -
        HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H) +
        HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c H)
      atTop (nhds (pintzZetaAFETermNumerator s base n 0)) := by
    simpa using (tendsto_const_nhds.sub hneg).add hpos
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  have hrect := pintzZetaAFETerm_finiteRectangle s base hn hq hc
    (show 0 < H by linarith) hbase
  rw [pintzZetaAFETerm_RectangleIntegral'_eq_edges] at hrect
  calc
    pintzZetaAFETermNumerator s base n 0 -
          HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H) +
          HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c H =
        pintzZetaAFETermVerticalTrunc s base n c H -
          pintzZetaAFETermVerticalTrunc s base n (-q) H := by
      linear_combination -hrect

/-- Finite termwise displacement.  This is the exact form used to move the
head of the zeta Dirichlet series to the left while leaving its tail on the
original right line. -/
theorem tendsto_pintzZetaAFETerm_vertical_difference_finset
    (s base : ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ => ∑ n ∈ S,
      (pintzZetaAFETermVerticalTrunc s base n c H -
        pintzZetaAFETermVerticalTrunc s base n (-q) H))
      atTop (nhds (∑ n ∈ S, pintzZetaAFETermNumerator s base n 0)) := by
  simpa using tendsto_finsetSum S (fun n hn =>
    tendsto_pintzZetaAFETerm_vertical_difference
      s base (hS n hn) hq hc hbase)

#print axioms pintzZetaAFETerm_RectangleIntegral'_eq_edges
#print axioms tendsto_pintzZetaAFETerm_vertical_difference
#print axioms tendsto_pintzZetaAFETerm_vertical_difference_finset

end

end GafniTao
