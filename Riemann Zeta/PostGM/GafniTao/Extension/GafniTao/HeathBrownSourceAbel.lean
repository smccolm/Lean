import GafniTao.HeathBrownAbelWeight

/-!
# Finite Abel summation on the source interval

Unlike the reusable frozen helper whose terminal weight lies one index beyond
its range, this identity is written on `1 ≤ h ≤ H`.  Consequently all
variation terms are genuine source edges and no `H+1` regularity is assumed.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrown_source_abel_identity
    (w a : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H) :
    (∑ h ∈ Finset.Icc 1 H, w h * a h) =
      w H * (∑ h ∈ Finset.Icc 1 H, a h) +
        ∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h) := by
  induction H with
  | zero => omega
  | succ H ih =>
      by_cases hHzero : H = 0
      · subst H
        simp
      · have hHpos : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hHzero
        have hih := ih hHpos
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ H)]
        rw [hih]
        ring

/-- Norm form of the preceding exact source-interval Abel identity. -/
theorem heathBrown_norm_source_weighted_le
    (w a : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H) (R D : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 H,
      ‖∑ h ∈ Finset.Icc 1 j, a h‖ ≤ R)
    (hweight : ‖w H‖ ≤ 1)
    (hvariation :
      (∑ j ∈ Finset.Ico 1 H, ‖w (j + 1) - w j‖) ≤ D) :
    ‖∑ h ∈ Finset.Icc 1 H, w h * a h‖ ≤ (1 + D) * R := by
  have hD : 0 ≤ D := by
    have hsum : 0 ≤ ∑ j ∈ Finset.Ico 1 H, ‖w (j + 1) - w j‖ := by positivity
    exact hsum.trans hvariation
  rw [heathBrown_source_abel_identity w a hH]
  calc
    ‖w H * (∑ h ∈ Finset.Icc 1 H, a h) +
        ∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ ≤
      ‖w H * (∑ h ∈ Finset.Icc 1 H, a h)‖ +
        ‖∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ := norm_add_le _ _
    _ ≤ R +
        ∑ j ∈ Finset.Ico 1 H,
          ‖w (j + 1) - w j‖ * R := by
      apply add_le_add
      · rw [norm_mul]
        calc
          ‖w H‖ * ‖∑ h ∈ Finset.Icc 1 H, a h‖ ≤ 1 * R :=
            mul_le_mul hweight (hpartial H (by simp [hH]))
              (norm_nonneg _) zero_le_one
          _ = R := one_mul R
      · calc
          ‖∑ j ∈ Finset.Ico 1 H,
              (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ ≤
            ∑ j ∈ Finset.Ico 1 H,
              ‖(w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Ico 1 H,
              ‖w (j + 1) - w j‖ * R := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul, norm_sub_rev]
            have hjIco := Finset.mem_Ico.mp hj
            exact mul_le_mul_of_nonneg_left
              (hpartial j (Finset.mem_Icc.mpr ⟨hjIco.1, hjIco.2.le⟩))
              (norm_nonneg _)
    _ = R +
        (∑ j ∈ Finset.Ico 1 H, ‖w (j + 1) - w j‖) * R := by
      rw [Finset.sum_mul]
    _ ≤ R + D * R := by gcongr
    _ = (1 + D) * R := by ring

/-- Partial-sum form of finite Abel summation.  Each edge keeps its own
partial sum, which is essential when those partial sums are averaged over
coefficient cells. -/
theorem heathBrown_norm_source_weighted_le_partial
    (w a : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H) (C : ℝ)
    (hweight : ‖w H‖ ≤ 1)
    (hedge : ∀ j ∈ Finset.Ico 1 H, ‖w (j + 1) - w j‖ ≤ C) :
    ‖∑ h ∈ Finset.Icc 1 H, w h * a h‖ ≤
      ‖∑ h ∈ Finset.Icc 1 H, a h‖ +
        C * ∑ j ∈ Finset.Ico 1 H,
          ‖∑ h ∈ Finset.Icc 1 j, a h‖ := by
  rw [heathBrown_source_abel_identity w a hH]
  calc
    _ ≤ ‖w H * (∑ h ∈ Finset.Icc 1 H, a h)‖ +
        ‖∑ j ∈ Finset.Ico 1 H,
          (w j - w (j + 1)) * (∑ h ∈ Finset.Icc 1 j, a h)‖ :=
      norm_add_le _ _
    _ ≤ ‖∑ h ∈ Finset.Icc 1 H, a h‖ +
        ∑ j ∈ Finset.Ico 1 H, C * ‖∑ h ∈ Finset.Icc 1 j, a h‖ := by
      apply add_le_add
      · rw [norm_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
      · calc
          _ ≤ ∑ j ∈ Finset.Ico 1 H,
              ‖(w j - w (j + 1)) *
                (∑ h ∈ Finset.Icc 1 j, a h)‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul, norm_sub_rev]
            exact mul_le_mul_of_nonneg_right (hedge j hj) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]

#print axioms heathBrown_source_abel_identity
#print axioms heathBrown_norm_source_weighted_le
#print axioms heathBrown_norm_source_weighted_le_partial

end

end GafniTao
