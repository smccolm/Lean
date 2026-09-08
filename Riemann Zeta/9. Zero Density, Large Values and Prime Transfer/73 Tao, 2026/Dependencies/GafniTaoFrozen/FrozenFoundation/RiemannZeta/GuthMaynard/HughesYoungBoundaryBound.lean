import RiemannZeta.GuthMaynard.HughesYoungBoundaryFar

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative equation-(65) estimates for the initial smooth boxes
-/

/-- The full integrated equation-(65) estimate for a mixed box whose left
coordinate is the isolated lower endpoint.  The initial scale is positive,
and the entire box is the far family by the preceding lattice theorem. -/
theorem exists_hughesYoung_initial_left_box_full_bound
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T c H Y : ℝ} {h k M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 4 * Cγ * c ≤ 1 →
      0 ≤ H → H ≤ T / 8 → 1 ≤ Y →
      0 < h → 0 < k →
      (T / (5 * T)) ^ j *
          ‖hughesYoungLocalizedOffDiagonalBox T c H
            (1 / hughesYoungDyadicRatio) Y h k M N‖ ≤
        (((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L) *
          (D * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (((hughesYoungReducedLeft h k : ℕ) : ℝ) /
                (1 / hughesYoungDyadicRatio)) ^ ((1 / 2 : ℝ) + c) *
            (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
              ((1 / 2 : ℝ) + c)) := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T c H Y h k M N hT hc hc1 hsmall hH hHT hY hh hk
  have hT0 : 0 < T := by linarith
  rw [hughesYoungLocalizedOffDiagonalBox_initial_left_eq_far
    (P := T) hh hk hY]
  exact hfar (T := T) (c := c) (H := H) (P := T)
    (X := 1 / hughesYoungDyadicRatio) (Y := Y)
    (h := h) (k := k)
    (a := hughesYoungReducedLeft h k)
    (b := hughesYoungReducedRight h k) (M := M) (N := N)
    hT hc hc1 hsmall hH hHT hT0 le_rfl
    (div_pos zero_lt_one hughesYoungDyadicRatio_pos)
    (lt_of_lt_of_le zero_lt_one hY) hh hk
    (hughesYoungReducedLeft_pos hh)
    (hughesYoungReducedRight_pos hh hk)

/-- Symmetric full bound for a mixed box whose right coordinate is the
initial smooth endpoint box. -/
theorem exists_hughesYoung_initial_right_box_full_bound
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧ ∃ Cw : ℕ → ℝ,
      (∀ i, 0 < Cw i) ∧
      ∀ {T c H X : ℝ} {h k M N : ℕ},
      16 ≤ T → 0 < c → c ≤ 1 → 4 * Cγ * c ≤ 1 →
      0 ≤ H → H ≤ T / 8 → 0 < X →
      0 < h → 0 < k →
      (T / (5 * T)) ^ j *
          ‖hughesYoungLocalizedOffDiagonalBox T c H
            X (1 / hughesYoungDyadicRatio) h k M N‖ ≤
        (((15 * T / 4) * c⁻¹ * Real.exp 100 * (6 * T) *
            hughesYoungHeightInputDerivativeConstant Cw j *
            ((T / 16)⁻¹) ^ j) * L) *
          (D * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
            ‖hughesYoungLocalizedStaticScalar T h k‖ *
            (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
              ((1 / 2 : ℝ) + c) *
            (((hughesYoungReducedRight h k : ℕ) : ℝ) /
                (1 / hughesYoungDyadicRatio)) ^ ((1 / 2 : ℝ) + c)) := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T c H X h k M N hT hc hc1 hsmall hH hHT hX hh hk
  have hT0 : 0 < T := by linarith
  rw [hughesYoungLocalizedOffDiagonalBox_initial_right_eq_far
    (P := T) hh]
  exact hfar (T := T) (c := c) (H := H) (P := T)
    (X := X) (Y := 1 / hughesYoungDyadicRatio)
    (h := h) (k := k)
    (a := hughesYoungReducedLeft h k)
    (b := hughesYoungReducedRight h k) (M := M) (N := N)
    hT hc hc1 hsmall hH hHT hT0 le_rfl hX
    (div_pos zero_lt_one hughesYoungDyadicRatio_pos) hh hk
    (hughesYoungReducedLeft_pos hh)
    (hughesYoungReducedRight_pos hh hk)

end RiemannZeta.GuthMaynard
