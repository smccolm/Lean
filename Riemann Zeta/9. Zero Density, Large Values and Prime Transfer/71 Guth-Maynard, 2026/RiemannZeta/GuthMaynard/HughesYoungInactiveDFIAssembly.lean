import RiemannZeta.GuthMaynard.HughesYoungNativeMoment

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# DFI assembly on the omitted Hughes--Young boxes

The passage from Hughes--Young (83) to (85) extends the product-truncated
dyadic family to the complete signed source.  This file keeps the omitted
boxes as one source family and applies the same DFI decomposition used on
the retained boxes.  In particular, no norm is taken before the literal
omitted shifted-divisor source has been compared with its signed central
continuation.
-/

/-- Omitted, source-valid boxes on which the optimized DFI scale and the
factor-four comparability conditions are available. -/
noncomputable def hughesYoungInactiveLargeDFIBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungInactiveRegularSupportedBoxes a b R K).filter fun ij =>
    64 ≤ hughesYoungDFIOptimalU P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) ∧
    hughesYoungFullDyadicScale ij.1 ≤
      4 * hughesYoungFullDyadicScale ij.2 ∧
    hughesYoungFullDyadicScale ij.2 ≤
      4 * hughesYoungFullDyadicScale ij.1

/-- The exact complementary family inside the omitted source-valid boxes. -/
noncomputable def hughesYoungInactiveNonLargeDFIBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungInactiveRegularSupportedBoxes a b R K).filter fun ij =>
    ¬ (64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1)

/-- Exact large/non-large partition of the omitted regular supported
family. -/
theorem hughesYoungInactiveRegularSupportedBoxes_eq_large_union_nonLarge
    (P : ℝ) (a b R K : ℕ) :
    hughesYoungInactiveRegularSupportedBoxes a b R K =
      hughesYoungInactiveLargeDFIBoxes P a b R K ∪
        hughesYoungInactiveNonLargeDFIBoxes P a b R K := by
  classical
  ext ij
  simp only [hughesYoungInactiveLargeDFIBoxes,
    hughesYoungInactiveNonLargeDFIBoxes, Finset.mem_union,
    Finset.mem_filter]
  tauto

/-- The two omitted-box subfamilies are disjoint. -/
theorem disjoint_hughesYoungInactiveLargeDFIBoxes_nonLarge
    (P : ℝ) (a b R K : ℕ) :
    Disjoint (hughesYoungInactiveLargeDFIBoxes P a b R K)
      (hughesYoungInactiveNonLargeDFIBoxes P a b R K) := by
  classical
  rw [Finset.disjoint_left]
  intro ij hlarge hsmall
  exact (Finset.mem_filter.mp hsmall).2 (Finset.mem_filter.mp hlarge).2

/-- Literal shifted-divisor source over the omitted large DFI boxes. -/
noncomputable def hughesYoungInactiveLargeDFIOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Literal shifted-divisor source over the omitted non-large boxes. -/
noncomputable def hughesYoungInactiveNonLargeDFIOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The literal shifted-divisor source over every omitted regular supported
box. -/
noncomputable def hughesYoungInactiveRegularSupportedOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungInactiveLargeDFIOffDiagonal T P R K +
    hughesYoungInactiveNonLargeDFIOffDiagonal T P R K

/-- The near signed DFI central term over the omitted large boxes. -/
noncomputable def hughesYoungInactiveLargeDFIPointwiseSignedCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The integrated DFI Theorem-1 discrepancy over the omitted large boxes. -/
noncomputable def hughesYoungInactiveLargeDFIPointwiseDiscrepancy
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseDFIDiscrepancyBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The equation-(65) far-shift source over the omitted large boxes. -/
noncomputable def hughesYoungInactiveLargeDFIFarOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete finite signed central family over the omitted large
boxes. -/
noncomputable def hughesYoungInactiveLargeDFIIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The equation-(65) central tail over the omitted large boxes. -/
noncomputable def hughesYoungInactiveLargeDFIIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2))

/-- Complete signed central source over the omitted non-large boxes. -/
noncomputable def hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedFiniteCompleteSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Equation-(65) central family over the omitted non-large boxes. -/
noncomputable def hughesYoungInactiveNonLargeDFIIntegratedCentralTail
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungInactiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungIntegratedPointwiseSignedCentral T
          (hughesYoungSmallContour T) (T / 8)
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFarShifts T P
            (hughesYoungFullDyadicScale ij.1)
            (hughesYoungFullDyadicScale ij.2)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            (hughesYoungFullDyadicBound ij.1)
            (hughesYoungFullDyadicBound ij.2))

/-- Exact DFI decomposition of the literal omitted large-box source. -/
theorem hughesYoungInactiveLargeDFIOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far
    (T P : ℝ) (R K : ℕ) :
    hughesYoungInactiveLargeDFIOffDiagonal T P R K =
      hughesYoungInactiveLargeDFIPointwiseSignedCentral T P R K +
        hughesYoungInactiveLargeDFIPointwiseDiscrepancy T P R K +
          hughesYoungInactiveLargeDFIFarOffDiagonal T P R K := by
  classical
  unfold hughesYoungInactiveLargeDFIOffDiagonal
    hughesYoungInactiveLargeDFIPointwiseSignedCentral
    hughesYoungInactiveLargeDFIPointwiseDiscrepancy
    hughesYoungInactiveLargeDFIFarOffDiagonal
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro ij _hij
  exact
    hughesYoungLocalizedOffDiagonalBox_eq_pointwiseCentral_add_discrepancy_add_far
      T (hughesYoungSmallContour T) (T / 8) P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
      (hh := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)

/-- Equation (81) on the omitted large boxes: the retained near central
family is the complete signed central family minus its far-shift tail. -/
theorem hughesYoungInactiveLargeDFIPointwiseSignedCentral_eq_complete_sub_tail
    {T P : ℝ} {R K : ℕ}
    (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) :
    hughesYoungInactiveLargeDFIPointwiseSignedCentral T P R K =
      hughesYoungInactiveLargeDFIIntegratedCompleteCentral T P R K -
        hughesYoungInactiveLargeDFIIntegratedCentralTail T P R K := by
  classical
  obtain ⟨hc, hc1, _hcinv⟩ := hughesYoungSmallContour_spec hT
  unfold hughesYoungInactiveLargeDFIPointwiseSignedCentral
    hughesYoungInactiveLargeDFIIntegratedCompleteCentral
    hughesYoungInactiveLargeDFIIntegratedCentralTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hhmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hkmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hh : 0 < h :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hlarge := (Finset.mem_filter.mp hij).2
  have hinactive := (Finset.mem_filter.mp hij).1
  have hrect := (Finset.mem_filter.mp hinactive).1
  have hsupported := (Finset.mem_filter.mp hrect).2
  have hi : 0 < ij.1 := hsupported.1
  have hj : 0 < ij.2 := hsupported.2.1
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ j
  obtain ⟨hscale, _hQ, _hUQ, _hQsq⟩ :=
    hughesYoungDFIOptimalScale_spec
      (lt_of_lt_of_le zero_lt_one hP)
      (zero_lt_one.trans_le hX) (zero_lt_one.trans_le hY) hlarge.1
  have hU : 0 < hughesYoungDFIOptimalU P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) := by
    linarith
  exact hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    hT16 hc hc1 (by positivity) le_rfl
      (lt_of_lt_of_le zero_lt_one hP) hPT hX hY hh hk
      hP hU hscale

/-- The retained near central family vanishes on every omitted non-large
box at the native Hughes--Young smoothing scale. -/
theorem hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_inactiveNonLarge
    {T : ℝ} {R K h k : ℕ} {ij : ℕ × ℕ}
    (hT : 0 < T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (hij : ij ∈ hughesYoungInactiveNonLargeDFIBoxes
      (hughesYoungDFISmoothingScale T)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K) :
    hughesYoungNearPointwiseSignedCentralBox T
        (hughesYoungSmallContour T) (T / 8)
        (hughesYoungDFISmoothingScale T)
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) h k
        (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) = 0 := by
  have hnot := (Finset.mem_filter.mp hij).2
  have hinactive := (Finset.mem_filter.mp hij).1
  have hrect := (Finset.mem_filter.mp hinactive).1
  have hsupported := (Finset.mem_filter.mp hrect).2
  have hX : 0 < hughesYoungFullDyadicScale ij.1 :=
    hughesYoungFullDyadicScale_pos ij.1
  have hY : 0 < hughesYoungFullDyadicScale ij.2 :=
    hughesYoungFullDyadicScale_pos ij.2
  by_cases hleft :
      4 * hughesYoungFullDyadicScale ij.2 <
        hughesYoungFullDyadicScale ij.1
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_left_separated
      hX hY hleft
  by_cases hright :
      4 * hughesYoungFullDyadicScale ij.1 <
        hughesYoungFullDyadicScale ij.2
  · exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_right_separated
      hX hY hright
  have hU : hughesYoungDFIOptimalU (hughesYoungDFISmoothingScale T)
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) < 64 := by
    by_contra hU
    apply hnot
    exact ⟨le_of_not_gt hU, le_of_not_gt hleft, le_of_not_gt hright⟩
  have hP : 0 < hughesYoungDFISmoothingScale T := by
    unfold hughesYoungDFISmoothingScale
    positivity
  have hYsmall : hughesYoungFullDyadicScale ij.2 <
      320 * hughesYoungDFISmoothingScale T :=
    hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
      hP hX hY (le_of_not_gt hright) hU
  exact hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_native_smallScale
    hT hsmall hY hYsmall

/-- On the omitted non-large boxes the complete signed central source is
exactly its equation-(65) far-shift extension. -/
theorem hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral_eq_tail
    {T : ℝ} (hT : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (R K : ℕ) :
    hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral T
        (hughesYoungDFISmoothingScale T) R K =
      hughesYoungInactiveNonLargeDFIIntegratedCentralTail T
        (hughesYoungDFISmoothingScale T) R K := by
  classical
  obtain ⟨hc, hc1, _hcinv⟩ := hughesYoungSmallContour_spec
    (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ T))
  unfold hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral
    hughesYoungInactiveNonLargeDFIIntegratedCentralTail
  apply Finset.sum_congr rfl
  intro h hhmem
  apply Finset.sum_congr rfl
  intro k hkmem
  apply Finset.sum_congr rfl
  intro ij hij
  have hh : 0 < h :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k :=
    Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
  have hinactive := (Finset.mem_filter.mp hij).1
  have hrect := (Finset.mem_filter.mp hinactive).1
  have hsupported := (Finset.mem_filter.mp hrect).2
  have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
    obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero hsupported.1.ne'
    rw [hiEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ i
  have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
    obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero hsupported.2.1.ne'
    rw [hjEq]
    simpa only [Nat.succ_eq_add_one] using
      one_le_hughesYoungFullDyadicScale_succ j
  let U : ℝ := (hughesYoungDFISmoothingScale T)⁻¹ *
    min (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have hEq := hughesYoungNearPointwiseSignedCentralBox_eq_integratedComplete_sub_far
    (T := T) (c := hughesYoungSmallContour T) (H := T / 8)
    (P := hughesYoungDFISmoothingScale T) (U := U)
    (X := hughesYoungFullDyadicScale ij.1)
    (Y := hughesYoungFullDyadicScale ij.2) (h := h) (k := k)
    (M := hughesYoungFullDyadicBound ij.1)
    (N := hughesYoungFullDyadicBound ij.2)
    hT hc hc1 (by positivity) le_rfl (lt_of_lt_of_le zero_lt_one hP)
    hPT hX hY hh hk hP hU le_rfl
  rw [hughesYoungNearPointwiseSignedCentralBox_eq_zero_of_inactiveNonLarge
    (lt_of_lt_of_le (by norm_num) hT) hsmall hij] at hEq
  exact sub_eq_zero.mp hEq.symm

/-- The omitted regular supported central source is exhausted by its large
and non-large DFI subfamilies. -/
theorem hughesYoungInactiveRegularSupportedIntegratedCompleteCentral_eq_large_add_nonLarge
    (T P : ℝ) (R K : ℕ) :
    hughesYoungInactiveRegularSupportedIntegratedCompleteCentral T R K =
      hughesYoungInactiveLargeDFIIntegratedCompleteCentral T P R K +
        hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral T P R K := by
  classical
  unfold hughesYoungInactiveRegularSupportedIntegratedCompleteCentral
    hughesYoungInactiveLargeDFIIntegratedCompleteCentral
    hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hughesYoungInactiveRegularSupportedBoxes_eq_large_union_nonLarge,
    Finset.sum_union
      (disjoint_hughesYoungInactiveLargeDFIBoxes_nonLarge P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)]

/-- Source-order DFI identity on all omitted regular supported boxes.  The
literal omitted shifted-divisor source remains on the right; this is the
term subsequently identified with the opening-line product tail. -/
theorem hughesYoungInactiveRegularSupportedIntegratedCompleteCentral_eq_source_sub_errors
    {T : ℝ} (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (R K : ℕ) :
    hughesYoungInactiveRegularSupportedIntegratedCompleteCentral T R K =
      hughesYoungInactiveRegularSupportedOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveLargeDFIPointwiseDiscrepancy T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveLargeDFIFarOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K +
        hughesYoungInactiveLargeDFIIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) R K +
        hughesYoungInactiveNonLargeDFIIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveNonLargeDFIOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K := by
  rw [hughesYoungInactiveRegularSupportedIntegratedCompleteCentral_eq_large_add_nonLarge
    T (hughesYoungDFISmoothingScale T) R K]
  have hcentral :=
    hughesYoungInactiveLargeDFIPointwiseSignedCentral_eq_complete_sub_tail
      (R := R) (K := K) hT hT16 hP hPT
  have hnonLarge :=
    hughesYoungInactiveNonLargeDFIIntegratedCompleteCentral_eq_tail
      hT16 hP hPT hsmall R K
  have hsource :=
    hughesYoungInactiveLargeDFIOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far
      T (hughesYoungDFISmoothingScale T) R K
  rw [hnonLarge]
  unfold hughesYoungInactiveRegularSupportedOffDiagonal
  linear_combination -hcentral - hsource

/-- The native Hughes--Young complementary source after DFI has also been
applied to the omitted regular boxes.  The only source-sized terms left are
the literal omitted shifted-divisor family and the exact dyadic endpoint
tail; all other summands are DFI discrepancies or equation-(65) tails. -/
theorem hughesYoungNativeComplementarySource_eq_inactiveSource_add_errors
    {T : ℝ} (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ hughesYoungDFISmoothingScale T)
    (hPT : hughesYoungDFISmoothingScale T ≤ T)
    (hsmall : 320 * hughesYoungDFISmoothingScale T *
        hughesYoungDFISmoothingScale T < T)
    (R K : ℕ) :
    hughesYoungNativeComplementarySource T
        (hughesYoungDFISmoothingScale T) R K =
      hughesYoungActiveNonLargeDFIOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungSupportedRegularNonLargeIntegratedCompleteCentral T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveRegularSupportedOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K +
        hughesYoungInactiveLargeDFIPointwiseDiscrepancy T
          (hughesYoungDFISmoothingScale T) R K +
        hughesYoungInactiveLargeDFIFarOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveLargeDFIIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungInactiveNonLargeDFIIntegratedCentralTail T
          (hughesYoungDFISmoothingScale T) R K +
        hughesYoungInactiveNonLargeDFIOffDiagonal T
          (hughesYoungDFISmoothingScale T) R K -
        hughesYoungFiniteRegularSupportedSourceTail T K := by
  rw [hughesYoungNativeComplementarySource_eq_supported_tails]
  rw [hughesYoungInactiveRegularSupportedIntegratedCompleteCentral_eq_source_sub_errors
    hT hT16 hP hPT hsmall R K]
  ring

end RiemannZeta.GuthMaynard
