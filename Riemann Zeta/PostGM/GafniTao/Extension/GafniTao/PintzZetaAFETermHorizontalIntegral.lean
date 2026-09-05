import GafniTao.PintzZetaAFETermHorizontal
import RiemannZeta.GuthMaynard.HughesYoungContourShift

/-!
# Vanishing horizontal integrals for individual AFE coefficients

The upper and lower horizontal sides tend to zero with the same explicit
quadratic-Gaussian majorant.  This is the limiting input for the termwise
rectangle identity.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The upper unnormalized horizontal integral of one positive Dirichlet
coefficient tends to zero. -/
theorem tendsto_pintzZetaAFETerm_HIntegral_zero
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ =>
      HIntegral (pintzZetaAFETermContourIntegrand s base n) (-q) c H)
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pintzZetaAFETerm_horizontal_bound s base hn hq hc hbase
  let A : ℝ := 100 * (max q c) ^ 2
  let B : ℝ := 2 + ‖base‖ + max q c
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (A - 100 * H ^ 2) * (B + H) ^ 16
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hmax : 0 ≤ max q c := (le_max_left q c).trans' hq.le
    positivity
  have henv : Tendsto envelope atTop (nhds 0) := by
    exact tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen C A B hC.le hB
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (pintzZetaAFETermContourIntegrand s base n) (-q) c H‖ ≤
        envelope H * |c - (-q)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.uIcc (-q) c := Set.uIoc_subset_uIcc hx
      simpa only [envelope, A, B, add_assoc] using hbound H hH x hx')
  simpa using henv.mul_const |c - (-q)|

/-- The lower unnormalized horizontal integral of one positive Dirichlet
coefficient tends to zero. -/
theorem tendsto_pintzZetaAFETerm_HIntegral_neg_zero
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ =>
      HIntegral (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H))
      atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pintzZetaAFETerm_horizontal_neg_bound s base hn hq hc hbase
  let A : ℝ := 100 * (max q c) ^ 2
  let B : ℝ := 2 + ‖base‖ + max q c
  let envelope : ℝ → ℝ := fun H =>
    C * Real.exp (A - 100 * H ^ 2) * (B + H) ^ 16
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hmax : 0 ≤ max q c := (le_max_left q c).trans' hq.le
    positivity
  have henv : Tendsto envelope atTop (nhds 0) := by
    exact tendsto_const_mul_exp_sub_sq_mul_shift_pow_sixteen C A B hC.le hB
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ H : ℝ in atTop,
      ‖HIntegral (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H)‖ ≤
        envelope H * |c - (-q)| by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
      unfold HIntegral
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Set.uIcc (-q) c := Set.uIoc_subset_uIcc hx
      simpa only [ofReal_neg, neg_mul, sub_eq_add_neg, envelope, A, B,
        add_assoc] using hbound H hH x hx')
  simpa using henv.mul_const |c - (-q)|

/-- The normalized upper horizontal integral tends to zero. -/
theorem tendsto_pintzZetaAFETerm_HIntegral'_zero
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ =>
      HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c H)
      atTop (nhds 0) := by
  unfold HIntegral'
  simpa using
    (tendsto_pintzZetaAFETerm_HIntegral_zero s base hn hq hc hbase).const_smul
      (1 / (2 * Real.pi * I))

/-- The normalized lower horizontal integral tends to zero. -/
theorem tendsto_pintzZetaAFETerm_HIntegral'_neg_zero
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    Tendsto (fun H : ℝ =>
      HIntegral' (pintzZetaAFETermContourIntegrand s base n) (-q) c (-H))
      atTop (nhds 0) := by
  unfold HIntegral'
  simpa using
    (tendsto_pintzZetaAFETerm_HIntegral_neg_zero s base hn hq hc hbase).const_smul
      (1 / (2 * Real.pi * I))

#print axioms tendsto_pintzZetaAFETerm_HIntegral_zero
#print axioms tendsto_pintzZetaAFETerm_HIntegral_neg_zero
#print axioms tendsto_pintzZetaAFETerm_HIntegral'_zero
#print axioms tendsto_pintzZetaAFETerm_HIntegral'_neg_zero

end

end GafniTao
