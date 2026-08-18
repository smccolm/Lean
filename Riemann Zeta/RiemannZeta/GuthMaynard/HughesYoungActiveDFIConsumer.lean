import RiemannZeta.GuthMaynard.HughesYoungActiveAssembly
import RiemannZeta.GuthMaynard.HughesYoungCanonicalBox

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Active Hughes--Young consumption of the exact DFI theorem

This module routes every regular active dyadic box through the exact
large/small scale split.  The large branch transitively consumes DFI
Theorem 1, including its signed equation-(27) central series and exact
equation-(30) error scale.
-/

/-- The explicit source majorant selected by the optimized DFI scale test
for one regular canonical box. -/
noncomputable def hughesYoungCanonicalRegularDFIMajorant
    (Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall : ℝ)
    (CwFar CwSmall : ℕ → ℝ) (j : ℕ)
    (T P ε : ℝ) (h k i l : ℕ) : ℝ :=
  if ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤
        2 * hughesYoungFullDyadicScale (i + 1) ∧
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤
        2 * hughesYoungFullDyadicScale (l + 1) then
    max 0 <| if 64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale (i + 1))
        (hughesYoungFullDyadicScale (l + 1)) then
      hughesYoungLargeBoxMajorant Cγnear Cnear Lnear CwFar Dfar Lfar
        j T P (hughesYoungFullDyadicScale (i + 1))
        (hughesYoungFullDyadicScale (l + 1)) ε h k
        (hughesYoungFullDyadicBound (i + 1))
        (hughesYoungFullDyadicBound (l + 1))
    else
      hughesYoungSmallBoxMajorant CwSmall Dsmall Lsmall j T
        (hughesYoungFullDyadicScale (i + 1))
        (hughesYoungFullDyadicScale (l + 1)) ε h k
        (hughesYoungFullDyadicBound (i + 1))
        (hughesYoungFullDyadicBound (l + 1))
  else 0

theorem hughesYoungCanonicalRegularDFIMajorant_nonneg
    (Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall : ℝ)
    (CwFar CwSmall : ℕ → ℝ) (j : ℕ)
    (T P ε : ℝ) (h k i l : ℕ) :
    0 ≤ hughesYoungCanonicalRegularDFIMajorant
      Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall
      CwFar CwSmall j T P ε h k i l := by
  by_cases hvalid :
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤
          2 * hughesYoungFullDyadicScale (i + 1) ∧
        ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤
          2 * hughesYoungFullDyadicScale (l + 1)
  · rw [hughesYoungCanonicalRegularDFIMajorant, if_pos hvalid]
    exact le_max_left _ _
  · rw [hughesYoungCanonicalRegularDFIMajorant, if_neg hvalid]

/-- Uniform regular-box consumer.  Its proof invokes the canonical scale
split, whose large branch invokes the exact native DFI error theorem. -/
theorem exists_norm_hughesYoungCanonicalRegularBox_le_dfiMajorant
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) (j : ℕ) :
    ∃ Cγnear Cnear Lnear Cγfar Dfar Lfar Cγsmall Dsmall Lsmall : ℝ,
      0 < Cγnear ∧ 0 < Cnear ∧ 0 < Lnear ∧
      0 < Cγfar ∧ 0 < Dfar ∧ 0 < Lfar ∧
      0 < Cγsmall ∧ 0 < Dsmall ∧ 0 < Lsmall ∧
      ∃ CwFar CwSmall : ℕ → ℝ,
        (∀ r, 0 < CwFar r) ∧ (∀ r, 0 < CwSmall r) ∧
      ∀ {T P : ℝ} {h k i l : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 0 < h → 0 < k →
      1 ≤ P → P ≤ T →
      4 * Cγfar * hughesYoungSmallContour T ≤ 1 →
      4 * Cγsmall * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale (i + 1))
          (hughesYoungFullDyadicScale (l + 1)) h k
          (hughesYoungFullDyadicBound (i + 1))
          (hughesYoungFullDyadicBound (l + 1))‖ ≤
        hughesYoungCanonicalRegularDFIMajorant
          Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall
          CwFar CwSmall j T P ε h k i l := by
  obtain ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
      Cγsmall, Dsmall, Lsmall,
      hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
      hCγsmall, hDsmall, hLsmall,
      CwFar, CwSmall, hCwFar, hCwSmall, hsplit⟩ :=
    exists_hughesYoungCanonicalRegularBox_scale_split ε hε0 hε4 j
  refine ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
    Cγsmall, Dsmall, Lsmall,
    hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
    hCγsmall, hDsmall, hLsmall,
    CwFar, CwSmall, hCwFar, hCwSmall, ?_⟩
  intro T P h k i l hT hT16 hh hk hP hPT hfar hsmall
  have hraw := hsplit (T := T) (P := P) (h := h) (k := k)
    (i := i) (j := l) hT hT16 hh hk hP hPT hfar hsmall
  unfold hughesYoungCanonicalRegularDFIMajorant
  rcases hraw with hzero | hlarge | hsmallBranch
  · rw [if_neg hzero.1, hzero.2, norm_zero]
  · rw [if_pos hlarge.1, if_pos hlarge.2.1]
    exact hlarge.2.2.trans (le_max_right _ _)
  · rw [if_pos hsmallBranch.1,
      if_neg (not_le_of_gt hsmallBranch.2.1)]
    exact hsmallBranch.2.2.trans (le_max_right _ _)

/-- Active boxes with both coordinates in the ordinary geometric part of
the partition. -/
noncomputable def hughesYoungActiveRegularBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter
    (fun ij => 0 < ij.1 ∧ 0 < ij.2)

/-- Active boxes meeting at least one isolated lower endpoint. -/
noncomputable def hughesYoungActiveBoundaryBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter
    (fun ij => ¬ (0 < ij.1 ∧ 0 < ij.2))

/-- The complete regular off-diagonal contribution at the source contour
height `T/8`. -/
noncomputable def hughesYoungActiveRegularOffDiagonal
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveRegularBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complementary lower-endpoint off-diagonal contribution. -/
noncomputable def hughesYoungActiveBoundaryOffDiagonal
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact partition of the global active off-diagonal family into regular
DFI boxes and isolated-endpoint boxes. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_regular_add_boundary
    (T : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungActiveRegularOffDiagonal T R K +
        hughesYoungActiveBoundaryOffDiagonal T R K := by
  classical
  unfold hughesYoungActiveFiniteOffDiagonal
    hughesYoungActiveDyadicOffDiagonal
    hughesYoungActiveRegularOffDiagonal
    hughesYoungActiveBoundaryOffDiagonal
    hughesYoungActiveRegularBoxes
    hughesYoungActiveBoundaryBoxes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_filter_add_sum_filter_not
    (s := hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (p := fun ij => 0 < ij.1 ∧ 0 < ij.2)
    (f := fun ij => hughesYoungLocalizedOffDiagonalBox T
      (hughesYoungSmallContour T) (T / 8)
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2))).symm

/-- The exact global regular-box majorant. -/
noncomputable def hughesYoungActiveRegularDFIMajorant
    (Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall : ℝ)
    (CwFar CwSmall : ℕ → ℝ) (j : ℕ)
    (T P ε : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveRegularBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungCanonicalRegularDFIMajorant
          Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall CwFar CwSmall
          j T P ε h k (ij.1 - 1) (ij.2 - 1)

/-- Every regular active box is now consumed by the exact DFI chain, and
the resulting inequalities are summed over the literal mollifier indices
and active dyadic family. -/
theorem exists_norm_hughesYoungActiveRegularOffDiagonal_le_dfiMajorant
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) (j : ℕ) :
    ∃ Cγnear Cnear Lnear Cγfar Dfar Lfar Cγsmall Dsmall Lsmall : ℝ,
      0 < Cγnear ∧ 0 < Cnear ∧ 0 < Lnear ∧
      0 < Cγfar ∧ 0 < Dfar ∧ 0 < Lfar ∧
      0 < Cγsmall ∧ 0 < Dsmall ∧ 0 < Lsmall ∧
      ∃ CwFar CwSmall : ℕ → ℝ,
        (∀ r, 0 < CwFar r) ∧ (∀ r, 0 < CwSmall r) ∧
      ∀ {T P : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ P → P ≤ T →
      4 * Cγfar * hughesYoungSmallContour T ≤ 1 →
      4 * Cγsmall * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungActiveRegularOffDiagonal T R K‖ ≤
        hughesYoungActiveRegularDFIMajorant
          Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall CwFar CwSmall
          j T P ε R K := by
  obtain ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
      Cγsmall, Dsmall, Lsmall,
      hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
      hCγsmall, hDsmall, hLsmall,
      CwFar, CwSmall, hCwFar, hCwSmall, hbox⟩ :=
    exists_norm_hughesYoungCanonicalRegularBox_le_dfiMajorant ε hε0 hε4 j
  refine ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
    Cγsmall, Dsmall, Lsmall,
    hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
    hCγsmall, hDsmall, hLsmall,
    CwFar, CwSmall, hCwFar, hCwSmall, ?_⟩
  intro T P R K hT hT16 hP hPT hfar hsmall
  classical
  unfold hughesYoungActiveRegularOffDiagonal
    hughesYoungActiveRegularDFIMajorant
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveRegularBoxes
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
              (T / 8) (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveRegularBoxes
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            ‖hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
              (T / 8) (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _hh =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk => norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ij hij
      have hijReg := (Finset.mem_filter.mp hij).2
      obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hijReg.1)
      obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hijReg.2)
      rw [hi, hl]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      exact hbox hT hT16
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
        hP hPT hfar hsmall

/-- The equation-(65) majorant after cancelling its positive integration by
parts prefactor.  This is used for either isolated endpoint orientation. -/
noncomputable def hughesYoungBoundaryBoxMajorant
    (Cw : ℕ → ℝ) (D L : ℝ) (j : ℕ)
    (T X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  max 0 ((T / (5 * T)) ^ (-(j : ℤ)) *
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N)

theorem norm_hughesYoungBoundaryBox_le_majorant_of_scaled
    {Cw : ℕ → ℝ} {D L T X Y ε : ℝ} {j h k M N : ℕ}
    (hT : 0 < T)
    (hscaled : (T / (5 * T)) ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N) :
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungBoundaryBoxMajorant Cw D L j T X Y ε h k M N := by
  let q : ℝ := T / (5 * T)
  have hq : 0 < q := div_pos hT (mul_pos (by norm_num) hT)
  have hqj : 0 < q ^ j := pow_pos hq j
  have hmul := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hqj.le)
  have hcancel : (q ^ j)⁻¹ * q ^ j = 1 := inv_mul_cancel₀ hqj.ne'
  have hzinv : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  unfold hughesYoungBoundaryBoxMajorant
  change _ ≤ max 0 (q ^ (-(j : ℤ)) *
    hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N)
  rw [hzinv]
  apply le_max_of_le_right
  calc
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ =
      (q ^ j)⁻¹ * (q ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8) X Y h k M N‖) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (q ^ j)⁻¹ *
        hughesYoungFarBoxMajorant Cw D L j T X Y ε h k M N := hmul

/-- Uniform left-endpoint equation-(65) consumer in cancelled form. -/
theorem exists_norm_hughesYoungInitialLeftBox_le_boundaryMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T Y : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ Y → 0 < h → 0 < k →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          (1 / hughesYoungDyadicRatio) Y h k M N‖ ≤
        hughesYoungBoundaryBoxMajorant Cw D L j T
          (1 / hughesYoungDyadicRatio) Y ε h k M N := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hbound⟩ :=
    exists_hughesYoung_initial_left_box_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T Y h k M N hT hT16 hY hh hk hsmall
  have hc := hughesYoungSmallContour_spec hT
  have hscaled := hbound (T := T) (c := hughesYoungSmallContour T)
    (H := T / 8) (Y := Y) (h := h) (k := k) (M := M) (N := N)
    hT16 hc.1 hc.2.1 hsmall (by positivity) le_rfl hY hh hk
  exact norm_hughesYoungBoundaryBox_le_majorant_of_scaled
    ((Real.exp_pos 1).trans_le hT) (by
      simpa only [hughesYoungFarBoxMajorant] using hscaled)

/-- Uniform right-endpoint equation-(65) consumer in cancelled form. -/
theorem exists_norm_hughesYoungInitialRightBox_le_boundaryMajorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ Cγ D L : ℝ, 0 < Cγ ∧ 0 < D ∧ 0 < L ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T X : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 1 ≤ X → 0 < h → 0 < k →
      4 * Cγ * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) (T / 8)
          X (1 / hughesYoungDyadicRatio) h k M N‖ ≤
        hughesYoungBoundaryBoxMajorant Cw D L j T
          X (1 / hughesYoungDyadicRatio) ε h k M N := by
  obtain ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, hbound⟩ :=
    exists_hughesYoung_initial_right_box_full_bound ε hε j
  refine ⟨Cγ, D, L, hCγ, hD, hL, Cw, hCw, ?_⟩
  intro T X h k M N hT hT16 hX hh hk hsmall
  have hc := hughesYoungSmallContour_spec hT
  have hscaled := hbound (T := T) (c := hughesYoungSmallContour T)
    (H := T / 8) (X := X) (h := h) (k := k) (M := M) (N := N)
    hT16 hc.1 hc.2.1 hsmall (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hX) hh hk
  exact norm_hughesYoungBoundaryBox_le_majorant_of_scaled
    ((Real.exp_pos 1).trans_le hT) (by
      simpa only [hughesYoungFarBoxMajorant] using hscaled)

/-- The box with both isolated endpoint coordinates has no off-diagonal
arithmetic lattice point. -/
theorem hughesYoungLocalizedOffDiagonalBox_initial_initial_eq_zero
    (T c H : ℝ) {h k M N : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungLocalizedOffDiagonalBox T c H
      (1 / hughesYoungDyadicRatio) (1 / hughesYoungDyadicRatio)
      h k M N = 0 := by
  classical
  unfold hughesYoungLocalizedOffDiagonalBox
    finiteQuadraticDivisorOffDiagonal
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hs : quadraticDivisorShift h k m n = 0
  · simp [hs]
  · simp only [hs, if_false]
    have hm0 : 0 < m := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1
    have hn0 : 0 < n := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
    let a := hughesYoungReducedLeft h k
    let b := hughesYoungReducedRight h k
    let d := hughesYoungCommonDivisor h k
    have ha0 : 0 < a := hughesYoungReducedLeft_pos hh
    have hb0 : 0 < b := hughesYoungReducedRight_pos hh hk
    have hd0 : 0 < d := hughesYoungCommonDivisor_pos hh
    have hhmul : h * m = d * (a * m) := by
      calc
        h * m = (d * a) * m := by
          rw [show d * a = h by
            exact hughesYoungCommonDivisor_mul_reducedLeft h k]
        _ = d * (a * m) := by ac_rfl
    have hkmul : k * n = d * (b * n) := by
      calc
        k * n = (d * b) * n := by
          rw [show d * b = k by
            exact hughesYoungCommonDivisor_mul_reducedRight h k]
        _ = d * (b * n) := by ac_rfl
    by_cases ham : a * m = 1
    · by_cases hbn : b * n = 1
      · have hshift : quadraticDivisorShift h k m n = 0 := by
          rw [quadraticDivisorShift_eq_zero_iff]
          rw [hhmul, hkmul, ham, hbn]
        exact (hs hshift).elim
      · have hbnPos : 0 < b * n := Nat.mul_pos hb0 hn0
        have hbnTwo : 2 ≤ b * n := by omega
        have hfull : hughesYoungFullDyadicCutoff 0 ((b * n : ℕ) : ℝ) = 0 := by
          rw [hughesYoungFullDyadicCutoff_zero_nat hbnPos]
          exact hughesYoungDyadicStep_nat_eq_zero_of_two_le hbnTwo
        have hcut : hughesYoungDyadicCutoffAt
            ((d : ℝ) * (1 / hughesYoungDyadicRatio)) ((k * n : ℕ) : ℝ) = 0 := by
          have hkmulR : ((k * n : ℕ) : ℝ) =
              (d : ℝ) * ((b * n : ℕ) : ℝ) := by
            exact_mod_cast hkmul
          calc
            hughesYoungDyadicCutoffAt
                ((d : ℝ) * (1 / hughesYoungDyadicRatio)) ((k * n : ℕ) : ℝ) =
              hughesYoungDyadicCutoffAt
                ((d : ℝ) * (1 / hughesYoungDyadicRatio))
                ((d : ℝ) * ((b * n : ℕ) : ℝ)) := by rw [hkmulR]
            _ = hughesYoungDyadicCutoffAt
                (1 / hughesYoungDyadicRatio) ((b * n : ℕ) : ℝ) :=
              hughesYoungDyadicCutoffAt_mul_cancel (by exact_mod_cast hd0)
            _ = hughesYoungFullDyadicCutoff 0 ((b * n : ℕ) : ℝ) := rfl
            _ = 0 := hfull
        unfold hughesYoungPreReducedIntegratedBoxWeight
        dsimp only
        rw [hcut]
        simp
    · have hamPos : 0 < a * m := Nat.mul_pos ha0 hm0
      have hamTwo : 2 ≤ a * m := by omega
      have hfull : hughesYoungFullDyadicCutoff 0 ((a * m : ℕ) : ℝ) = 0 := by
        rw [hughesYoungFullDyadicCutoff_zero_nat hamPos]
        exact hughesYoungDyadicStep_nat_eq_zero_of_two_le hamTwo
      have hcut : hughesYoungDyadicCutoffAt
          ((d : ℝ) * (1 / hughesYoungDyadicRatio)) ((h * m : ℕ) : ℝ) = 0 := by
        have hhmulR : ((h * m : ℕ) : ℝ) =
            (d : ℝ) * ((a * m : ℕ) : ℝ) := by
          exact_mod_cast hhmul
        calc
          hughesYoungDyadicCutoffAt
              ((d : ℝ) * (1 / hughesYoungDyadicRatio)) ((h * m : ℕ) : ℝ) =
            hughesYoungDyadicCutoffAt
              ((d : ℝ) * (1 / hughesYoungDyadicRatio))
              ((d : ℝ) * ((a * m : ℕ) : ℝ)) := by rw [hhmulR]
          _ = hughesYoungDyadicCutoffAt
              (1 / hughesYoungDyadicRatio) ((a * m : ℕ) : ℝ) :=
            hughesYoungDyadicCutoffAt_mul_cancel (by exact_mod_cast hd0)
          _ = hughesYoungFullDyadicCutoff 0 ((a * m : ℕ) : ℝ) := rfl
          _ = 0 := hfull
      unfold hughesYoungPreReducedIntegratedBoxWeight
      dsimp only
      rw [hcut]
      simp

/-- The complete explicit majorant for all active boxes meeting an isolated
lower endpoint.  The doubly isolated box contributes zero. -/
noncomputable def hughesYoungActiveBoundaryMajorant
    (CwLeft CwRight : ℕ → ℝ)
    (DLeft LLeft DRight LRight : ℝ) (j : ℕ)
    (T ε : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveBoundaryBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        if ij.1 = 0 then
          if ij.2 = 0 then 0 else
            hughesYoungBoundaryBoxMajorant CwLeft DLeft LLeft j T
              (1 / hughesYoungDyadicRatio)
              (hughesYoungFullDyadicScale ij.2) ε h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)
        else
          hughesYoungBoundaryBoxMajorant CwRight DRight LRight j T
            (hughesYoungFullDyadicScale ij.1)
            (1 / hughesYoungDyadicRatio) ε h k
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2)

/-- The two one-sided equation-(65) estimates sum to a bound for the literal
active boundary family.  The proof uses the exact zero theorem for the
double endpoint and derives the remaining endpoint orientation from
membership in the boundary filter. -/
theorem exists_norm_hughesYoungActiveBoundaryOffDiagonal_le_majorant
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    ∃ CγLeft DLeft LLeft CγRight DRight LRight : ℝ,
      0 < CγLeft ∧ 0 < DLeft ∧ 0 < LLeft ∧
      0 < CγRight ∧ 0 < DRight ∧ 0 < LRight ∧
      ∃ CwLeft CwRight : ℕ → ℝ,
        (∀ i, 0 < CwLeft i) ∧ (∀ i, 0 < CwRight i) ∧
      ∀ {T : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T →
      4 * CγLeft * hughesYoungSmallContour T ≤ 1 →
      4 * CγRight * hughesYoungSmallContour T ≤ 1 →
      ‖hughesYoungActiveBoundaryOffDiagonal T R K‖ ≤
        hughesYoungActiveBoundaryMajorant CwLeft CwRight
          DLeft LLeft DRight LRight j T ε R K := by
  obtain ⟨CγLeft, DLeft, LLeft, hCγLeft, hDLeft, hLLeft,
      CwLeft, hCwLeft, hleft⟩ :=
    exists_norm_hughesYoungInitialLeftBox_le_boundaryMajorant ε hε j
  obtain ⟨CγRight, DRight, LRight, hCγRight, hDRight, hLRight,
      CwRight, hCwRight, hright⟩ :=
    exists_norm_hughesYoungInitialRightBox_le_boundaryMajorant ε hε j
  refine ⟨CγLeft, DLeft, LLeft, CγRight, DRight, LRight,
    hCγLeft, hDLeft, hLLeft, hCγRight, hDRight, hLRight,
    CwLeft, CwRight, hCwLeft, hCwRight, ?_⟩
  intro T R K hT hT16 hsmallLeft hsmallRight
  classical
  unfold hughesYoungActiveBoundaryOffDiagonal
    hughesYoungActiveBoundaryMajorant
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveBoundaryBoxes
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            hughesYoungLocalizedOffDiagonalBox T
              (hughesYoungSmallContour T) (T / 8)
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveBoundaryBoxes
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            ‖hughesYoungLocalizedOffDiagonalBox T
              (hughesYoungSmallContour T) (T / 8)
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      apply Finset.sum_le_sum
      intro ij hij
      have hh : 0 < h :=
        Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
      have hk : 0 < k :=
        Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
      have hboundary := (Finset.mem_filter.mp hij).2
      by_cases hi : ij.1 = 0
      · by_cases hl : ij.2 = 0
        · simp only [hi, hl, if_pos]
          have hz :=
            hughesYoungLocalizedOffDiagonalBox_initial_initial_eq_zero
              T (hughesYoungSmallContour T) (T / 8)
              (M := hughesYoungFullDyadicBound 0)
              (N := hughesYoungFullDyadicBound 0) hh hk
          simp only [hughesYoungFullDyadicScale, hz, norm_zero]
          exact le_rfl
        · obtain ⟨l, hlEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero hl
          simp only [hi, if_pos, hl, if_false]
          rw [hlEq]
          exact hleft hT hT16
            (one_le_hughesYoungFullDyadicScale_succ l) hh hk hsmallLeft
      · have hiPos : 0 < ij.1 := Nat.pos_of_ne_zero hi
        have hl : ij.2 = 0 := by
          by_contra hl
          exact hboundary ⟨hiPos, Nat.pos_of_ne_zero hl⟩
        obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi
        simp only [hi, if_false, hl]
        rw [hiEq]
        exact hright hT hT16
          (one_le_hughesYoungFullDyadicScale_succ i) hh hk hsmallRight

/-- Regular DFI and isolated-boundary estimates combine without losing the
literal finite active off-diagonal object. -/
theorem norm_hughesYoungActiveFiniteOffDiagonal_le_regular_add_boundary
    {T P ε : ℝ} {R K j : ℕ}
    {Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall : ℝ}
    {CwFar CwSmall CwLeft CwRight : ℕ → ℝ}
    {DLeft LLeft DRight LRight : ℝ}
    (hregular : ‖hughesYoungActiveRegularOffDiagonal T R K‖ ≤
      hughesYoungActiveRegularDFIMajorant
        Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall CwFar CwSmall
        j T P ε R K)
    (hboundary : ‖hughesYoungActiveBoundaryOffDiagonal T R K‖ ≤
      hughesYoungActiveBoundaryMajorant CwLeft CwRight
        DLeft LLeft DRight LRight j T ε R K) :
    ‖hughesYoungActiveFiniteOffDiagonal T (T / 8) R K‖ ≤
      hughesYoungActiveRegularDFIMajorant
          Cγnear Cnear Lnear Dfar Lfar Dsmall Lsmall CwFar CwSmall
          j T P ε R K +
        hughesYoungActiveBoundaryMajorant CwLeft CwRight
          DLeft LLeft DRight LRight j T ε R K := by
  rw [hughesYoungActiveFiniteOffDiagonal_eq_regular_add_boundary]
  exact (norm_add_le _ _).trans (add_le_add hregular hboundary)

end RiemannZeta.GuthMaynard
