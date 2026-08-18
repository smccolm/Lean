import RiemannZeta.GuthMaynard.HughesYoungIntegratedDiscrepancy
import RiemannZeta.GuthMaynard.HughesYoungSignedCentralGlobal
import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Source-order Hughes--Young consumption of DFI

Hughes--Young apply the quadratic-divisor theorem before integrating in the
compact Mellin ordinate.  These definitions therefore use the pointwise
signed central series and the literal pointwise DFI discrepancy from
`HughesYoungIntegratedDiscrepancy`, rather than taking norms of the four
central terms separately.
-/

/-- The signed DFI equation-(27) contribution of one near-shift box, with
the compact Mellin integral kept outside the complete signed shift sum. -/
noncomputable def hughesYoungNearPointwiseSignedCentralBox
    (T c H P X Y : ℝ) (h k M N : ℕ) : ℂ :=
  hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k
    (hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)

/-- The literal integrated DFI Theorem-1 error of one near-shift box. -/
noncomputable def hughesYoungNearPointwiseDFIDiscrepancyBox
    (T c H P X Y : ℝ) (h k M N : ℕ) : ℂ :=
  hughesYoungIntegratedPointwiseDFIDiscrepancy T c H X Y h k M N
    (hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)

/-- Exact source-order split of the near shifts. -/
theorem hughesYoungNearShiftSum_eq_pointwiseCentral_add_discrepancy
    (T c H P X Y : ℝ) (h k M N : ℕ) :
    (∑ r ∈ hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r) =
      hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N +
        hughesYoungNearPointwiseDFIDiscrepancyBox
          T c H P X Y h k M N := by
  exact
    sum_dfiDyadicShiftedDivisorSum_gcdReducedIntegratedBox_eq_pointwiseCentral_add_discrepancy
      T c H X Y h k M N
      (hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)

/-- Exact cancellation-preserving decomposition of one localized
off-diagonal box in the order used in Hughes--Young Sections 5--6. -/
theorem hughesYoungLocalizedOffDiagonalBox_eq_pointwiseCentral_add_discrepancy_add_far
    (T c H P X Y : ℝ) {h k M N : ℕ} (hh : 0 < h) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N =
      hughesYoungNearPointwiseSignedCentralBox T c H P X Y h k M N +
        hughesYoungNearPointwiseDFIDiscrepancyBox T c H P X Y h k M N +
          hughesYoungFarOffDiagonalBox T c H P X Y h k M N := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    T c H P X Y hh]
  rw [hughesYoungNearShiftSum_eq_pointwiseCentral_add_discrepancy]
  rfl

/-- The complete source-order signed DFI contribution in the active finite
Hughes--Young expansion. -/
noncomputable def hughesYoungActiveFinitePointwiseSignedCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete literal DFI error in the active finite Hughes--Young
expansion, after the compact Mellin integration but before any triangle
inequality is applied to the signed main term. -/
noncomputable def hughesYoungActiveFinitePointwiseDFIDiscrepancy
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseDFIDiscrepancyBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact global source-order DFI split of the concrete active
off-diagonal term. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungActiveFinitePointwiseSignedCentral T P R K +
        hughesYoungActiveFinitePointwiseDFIDiscrepancy T P R K +
          hughesYoungActiveFiniteFarOffDiagonal T P R K := by
  classical
  unfold hughesYoungActiveFiniteOffDiagonal
    hughesYoungActiveFinitePointwiseSignedCentral
    hughesYoungActiveFinitePointwiseDFIDiscrepancy
    hughesYoungActiveFiniteFarOffDiagonal
    hughesYoungActiveDyadicOffDiagonal
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

/-- On a large DFI box, the concrete near-shift discrepancy is bounded by
the exact DFI Theorem-1 error scale.  The signed central contribution does
not occur on the right-hand side. -/
theorem exists_uniform_norm_hughesYoungNearPointwiseDFIDiscrepancyBox
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T X Y P : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P → 64 ≤ hughesYoungDFIOptimalU P X Y →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X →
      (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y →
      ‖hughesYoungNearPointwiseDFIDiscrepancyBox T
          (hughesYoungSmallContour T) (T / 8) P X Y h k M N‖ ≤
        (T * (Real.log T * Real.exp (4 * Cγ) *
          ((hughesYoungReducedLeft h k : ℝ) / X) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          ((hughesYoungReducedRight h k : ℝ) / Y) ^
            ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
          (((hughesYoungNearShifts T P X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N).card : ℝ) *
            (‖hughesYoungLocalizedStaticScalar T h k‖ *
              (C * dfiTheorem1ErrorScale P X Y ε)))) * L := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hsource⟩ :=
    exists_uniform_norm_hughesYoungSmallContourPointwiseDFIDiscrepancy
      ε hε0 hε4
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T X Y P h k M N hT hX hY hh hk hP hlarge hM hN haX hbY
  obtain ⟨hscale, hQ, hUQ, hQsq⟩ :=
    hughesYoungDFIOptimalScale_spec
      (lt_of_lt_of_le zero_lt_one hP)
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hlarge
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hU0 : 0 < hughesYoungDFIOptimalU P X Y := by linarith
  unfold hughesYoungNearPointwiseDFIDiscrepancyBox
  exact hsource hT (by positivity) hX hY hh hk hP
    hU0 hscale hQ hUQ hQsq hM hN haX hbY
    hughesYoungNearShifts_dfi_conditions

/-- The explicit small-contour majorant for the signed equation-(27)
contribution of one concrete near-shift box. -/
noncomputable def hughesYoungPointwiseSignedCentralMajorant
    (Cγ C L T P X Y : ℝ) (h k M N : ℕ) : ℝ :=
  (T * (Real.log T * Real.exp (4 * Cγ) *
    ((hughesYoungReducedLeft h k : ℝ) / X) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((hughesYoungReducedRight h k : ℝ) / Y) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
    (∑ r ∈ hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
        (C * (hughesYoungCentralArithmeticScale X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            r.natAbs +
          hughesYoungCentralArithmeticScale Y X
            (hughesYoungReducedRight h k) (hughesYoungReducedLeft h k)
            r.natAbs)))) * L

/-- Exact large-box consumer for the signed DFI equation-(27) term.  Its
left-hand side is the same `hughesYoungNearPointwiseSignedCentralBox` used
by the global off-diagonal decomposition. -/
theorem exists_uniform_norm_hughesYoungNearPointwiseSignedCentralBox :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T X Y P : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P → 64 ≤ hughesYoungDFIOptimalU P X Y →
      (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X →
      (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y →
      ‖hughesYoungNearPointwiseSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8) P X Y h k M N‖ ≤
        hughesYoungPointwiseSignedCentralMajorant
          Cγ C L T P X Y h k M N := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hsource⟩ :=
    exists_uniform_norm_hughesYoungSmallContourPointwiseSignedCentral
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T X Y P h k M N hT hX hY hh hk hP hlarge haX hbY
  obtain ⟨hscale, _hQ, _hUQ, _hQsq⟩ :=
    hughesYoungDFIOptimalScale_spec
      (lt_of_lt_of_le zero_lt_one hP)
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hlarge
  have hU0 : 0 < hughesYoungDFIOptimalU P X Y := by linarith
  have hs : ∀ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      r ≠ 0 ∧ |(r : ℝ)| ≤ Y / 2 ∧ T * (|(r : ℝ)| / Y) ≤ P := by
    intro r hr
    obtain ⟨hr0, hrY, hrP, _hrPos, _hrNeg⟩ :=
      hughesYoungNearShifts_dfi_conditions r hr
    exact ⟨hr0, hrY, hrP⟩
  unfold hughesYoungNearPointwiseSignedCentralBox
    hughesYoungPointwiseSignedCentralMajorant
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  exact hsource hT (div_nonneg hT0.le (by norm_num)) hX hY hh hk hP
    hU0 hscale haX hbY hs

/-- The active boxes on which the optimized DFI scale is genuinely
available and the two physical dyadic scales have the comparability used
before Hughes--Young (78).  Boundary, support-empty, noncomparable, and
small-optimal-scale boxes are not silently passed through DFI; they remain
in the complementary source sum. -/
noncomputable def hughesYoungActiveLargeDFIBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter fun ij =>
    0 < ij.1 ∧ 0 < ij.2 ∧
    (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
    (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2 ∧
    64 ≤ hughesYoungDFIOptimalU P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) ∧
    hughesYoungFullDyadicScale ij.1 ≤
      4 * hughesYoungFullDyadicScale ij.2 ∧
    hughesYoungFullDyadicScale ij.2 ≤
      4 * hughesYoungFullDyadicScale ij.1

/-- All active boxes not belonging to the exact large-DFI range. -/
noncomputable def hughesYoungActiveNonLargeDFIBoxes
    (P : ℝ) (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  (hughesYoungActiveDyadicBoxes a b R K).filter fun ij =>
    ¬ (0 < ij.1 ∧ 0 < ij.2 ∧
      (a : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.1 ∧
      (b : ℝ) ≤ 2 * hughesYoungFullDyadicScale ij.2 ∧
      64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1)

/-- The concrete active off-diagonal restricted to boxes satisfying every
large-DFI entry condition. -/
noncomputable def hughesYoungActiveLargeDFIOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complementary active box family, retained as its literal source
sum for the small-box and boundary estimates. -/
noncomputable def hughesYoungActiveNonLargeDFIOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveNonLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungLocalizedOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact partition of the concrete active off-diagonal into the large-DFI
family and its literal complement. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_largeDFI_add_nonLargeDFI
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungActiveLargeDFIOffDiagonal T P R K +
        hughesYoungActiveNonLargeDFIOffDiagonal T P R K := by
  classical
  unfold hughesYoungActiveFiniteOffDiagonal
    hughesYoungActiveDyadicOffDiagonal
    hughesYoungActiveLargeDFIOffDiagonal
    hughesYoungActiveNonLargeDFIOffDiagonal
    hughesYoungActiveLargeDFIBoxes
    hughesYoungActiveNonLargeDFIBoxes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  exact (Finset.sum_filter_add_sum_filter_not
    (s := hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
    (p := fun ij =>
      0 < ij.1 ∧ 0 < ij.2 ∧
      (hughesYoungReducedLeft h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.1 ∧
      (hughesYoungReducedRight h k : ℝ) ≤
        2 * hughesYoungFullDyadicScale ij.2 ∧
      64 ≤ hughesYoungDFIOptimalU P
        (hughesYoungFullDyadicScale ij.1)
        (hughesYoungFullDyadicScale ij.2) ∧
      hughesYoungFullDyadicScale ij.1 ≤
        4 * hughesYoungFullDyadicScale ij.2 ∧
      hughesYoungFullDyadicScale ij.2 ≤
        4 * hughesYoungFullDyadicScale ij.1)
    (f := fun ij => hughesYoungLocalizedOffDiagonalBox T
      (hughesYoungSmallContour T) (T / 8)
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2))).symm

/-- The signed central contribution over exactly the large-DFI active
boxes. -/
noncomputable def hughesYoungActiveLargeDFIPointwiseSignedCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseSignedCentralBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Finite sum of the exact signed-central box majorants over precisely the
large/comparable DFI family. -/
noncomputable def hughesYoungActiveLargeDFISignedCentralMajorant
    (Cγ C L T P : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungPointwiseSignedCentralMajorant Cγ C L T P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Global consumer of the exact signed equation-(27) contribution on all
boxes where the optimized DFI scale is available. -/
theorem exists_norm_hughesYoungActiveLargeDFIPointwiseSignedCentral_le :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T P : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 1 ≤ P →
      ‖hughesYoungActiveLargeDFIPointwiseSignedCentral T P R K‖ ≤
        hughesYoungActiveLargeDFISignedCentralMajorant Cγ C L T P R K := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hbox⟩ :=
    exists_uniform_norm_hughesYoungNearPointwiseSignedCentralBox
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T P R K hT hP
  classical
  unfold hughesYoungActiveLargeDFIPointwiseSignedCentral
    hughesYoungActiveLargeDFISignedCentralMajorant
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            hughesYoungNearPointwiseSignedCentralBox T
              (hughesYoungSmallContour T) (T / 8) P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            ‖hughesYoungNearPointwiseSignedCentralBox T
              (hughesYoungSmallContour T) (T / 8) P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _hh =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk =>
            norm_sum_le _ _))
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
      have hp := (Finset.mem_filter.mp hij).2
      have hi : 0 < ij.1 := hp.1
      have hj : 0 < ij.2 := hp.2.1
      have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
        obtain ⟨i, hiEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        rw [hiEq]
        simpa only [Nat.succ_eq_add_one] using
          one_le_hughesYoungFullDyadicScale_succ i
      have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
        obtain ⟨j, hjEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
        rw [hjEq]
        simpa only [Nat.succ_eq_add_one] using
          one_le_hughesYoungFullDyadicScale_succ j
      exact hbox hT hX hY hh hk hP hp.2.2.2.2.1 hp.2.2.1 hp.2.2.2.1

/-- The exact integrated DFI discrepancy over the large-DFI active boxes. -/
noncomputable def hughesYoungActiveLargeDFIPointwiseDiscrepancy
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearPointwiseDFIDiscrepancyBox T
          (hughesYoungSmallContour T) (T / 8) P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The equation-(65) far contribution over the large-DFI active boxes. -/
noncomputable def hughesYoungActiveLargeDFIFarOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact source-order DFI decomposition on precisely the boxes where the
optimized DFI scale is available. -/
theorem hughesYoungActiveLargeDFIOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveLargeDFIOffDiagonal T P R K =
      hughesYoungActiveLargeDFIPointwiseSignedCentral T P R K +
        hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K +
          hughesYoungActiveLargeDFIFarOffDiagonal T P R K := by
  classical
  unfold hughesYoungActiveLargeDFIOffDiagonal
    hughesYoungActiveLargeDFIPointwiseSignedCentral
    hughesYoungActiveLargeDFIPointwiseDiscrepancy
    hughesYoungActiveLargeDFIFarOffDiagonal
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

/-- The exact pointwise-DFI error majorant for one concrete box. -/
noncomputable def hughesYoungPointwiseDFIErrorMajorant
    (Cγ C L ε T P X Y : ℝ) (h k M N : ℕ) : ℝ :=
  (T * (Real.log T * Real.exp (4 * Cγ) *
    ((hughesYoungReducedLeft h k : ℝ) / X) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((hughesYoungReducedRight h k : ℝ) / Y) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
    (((hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      M N).card : ℝ) *
      (‖hughesYoungLocalizedStaticScalar T h k‖ *
        (C * dfiTheorem1ErrorScale P X Y ε)))) * L

/-- The real-valued form of the sharp equation-(79) shift count.  The
absence of the zero shift is essential: after multiplication by the height
factor, `T` cancels without an additive remainder. -/
theorem cast_card_hughesYoungNearShifts_le_two_mul_div
    {T P X Y : ℝ} {a b M N : ℕ}
    (hT : 0 < T) (hP : 0 ≤ P) (hY : 0 < Y) :
    ((hughesYoungNearShifts T P X Y a b M N).card : ℝ) ≤
      2 * P * Y / T := by
  have hcard := card_hughesYoungNearShifts_le_two_mul_floor
    (T := T) (P := P) (X := X) (Y := Y)
    (a := a) (b := b) (M := M) (N := N) hT hY
  have hcast :
      ((hughesYoungNearShifts T P X Y a b M N).card : ℝ) ≤
        (2 * ⌊P * Y / T⌋₊ : ℕ) := by
    exact_mod_cast hcard
  calc
    ((hughesYoungNearShifts T P X Y a b M N).card : ℝ) ≤
        (2 * ⌊P * Y / T⌋₊ : ℕ) := hcast
    _ = 2 * (⌊P * Y / T⌋₊ : ℝ) := by push_cast; ring
    _ ≤ 2 * (P * Y / T) := by
      gcongr
      exact Nat.floor_le (by positivity)
    _ = 2 * P * Y / T := by ring

/-- On the small contour, the extra exponent in a normalized dyadic
coordinate costs at most a factor two; the square-root normalization is
kept intact for the Hughes--Young `(hkMN)^(3/8)` calculation. -/
theorem rpow_half_add_le_two_mul_rpow_half
    {x c : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    x ^ ((1 / 2 : ℝ) + c) ≤ 2 * x ^ (1 / 2 : ℝ) := by
  rw [Real.rpow_add hx]
  have hxc : x ^ c ≤ 2 := by
    calc
      x ^ c ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow hx.le hx2 hc0
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
      _ = 2 := Real.rpow_one 2
  calc
    x ^ (1 / 2 : ℝ) * x ^ c ≤ x ^ (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hxc (Real.rpow_nonneg hx.le _)
    _ = 2 * x ^ (1 / 2 : ℝ) := by ring

/-- Exact square-root normalization of the two Hughes--Young dyadic
coordinates. -/
theorem mul_div_rpow_half_eq_mul_rpow_mul_product_rpow_neg_half
    {a b X Y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (hY : 0 < Y) :
    (a / X) ^ (1 / 2 : ℝ) * (b / Y) ^ (1 / 2 : ℝ) =
      (a * b) ^ (1 / 2 : ℝ) * (X * Y) ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow ha.le hX.le, Real.div_rpow hb.le hY.le,
    Real.mul_rpow ha.le hb.le, Real.mul_rpow hX.le hY.le,
    Real.rpow_neg hX.le, Real.rpow_neg hY.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hX _),
    ne_of_gt (Real.rpow_pos_of_pos hY _)]

/-- The comparable-scale calculation in Hughes--Young (78)--(80).  It is
kept as an explicit real-power inequality so the later finite summation
cannot accidentally replace `X ≍ Y` by an unsupported global claim. -/
theorem y_mul_sum_rpow_quarter_mul_product_rpow_le
    {X Y ε : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ≤ 4 * Y) (hYX : Y ≤ 4 * X) :
    Y * (X + Y) ^ (1 / 4 : ℝ) *
        (X * Y) ^ (-(1 / 4 : ℝ) + ε) ≤
      (2 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
        (X * Y) ^ (3 / 8 + ε) := by
  have hProd : 0 < X * Y := mul_pos hX hY
  have hYsq : Y ^ 2 ≤ 4 * (X * Y) := by
    have := mul_le_mul_of_nonneg_right hYX hY.le
    nlinarith
  have hXsq : X ^ 2 ≤ 4 * (X * Y) := by
    have := mul_le_mul_of_nonneg_right hXY hX.le
    nlinarith
  have hsqrtSq : (Real.sqrt (X * Y)) ^ 2 = X * Y := by
    rw [Real.sq_sqrt hProd.le]
  have hYroot : Y ≤ 2 * Real.sqrt (X * Y) := by
    have hs0 := Real.sqrt_nonneg (X * Y)
    nlinarith
  have hXroot : X ≤ 2 * Real.sqrt (X * Y) := by
    have hs0 := Real.sqrt_nonneg (X * Y)
    nlinarith
  have hsum : X + Y ≤ 4 * Real.sqrt (X * Y) := by linarith
  have hsumPow : (X + Y) ^ (1 / 4 : ℝ) ≤
      (4 : ℝ) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 8 : ℝ) := by
    have hsum0 : 0 ≤ X + Y := by positivity
    calc
      (X + Y) ^ (1 / 4 : ℝ) ≤
          (4 * Real.sqrt (X * Y)) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow hsum0 hsum (by norm_num)
      _ = (4 : ℝ) ^ (1 / 4 : ℝ) *
          (Real.sqrt (X * Y)) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _)]
      _ = (4 : ℝ) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 8 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hProd.le]
        congr 2
        ring
  have hYpow : Y ≤ 2 * (X * Y) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using hYroot
  calc
    Y * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (-(1 / 4 : ℝ) + ε) ≤
        (2 * (X * Y) ^ (1 / 2 : ℝ)) *
          ((4 : ℝ) ^ (1 / 4 : ℝ) * (X * Y) ^ (1 / 8 : ℝ)) *
          (X * Y) ^ (-(1 / 4 : ℝ) + ε) := by
      gcongr
    _ = (2 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
        ((X * Y) ^ (1 / 2 : ℝ) * (X * Y) ^ (1 / 8 : ℝ) *
          (X * Y) ^ (-(1 / 4 : ℝ) + ε)) := by ring
    _ = (2 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
        (X * Y) ^ (3 / 8 + ε) := by
      rw [← Real.rpow_add hProd, ← Real.rpow_add hProd]
      congr 1
      ring_nf

/-- The explicit right side obtained from Hughes--Young (79)--(80) for one
comparable dyadic box, after the sharp shift count has been performed. -/
noncomputable def hughesYoungEquation80BoxErrorMajorant
    (Cγ C L ε T P X Y : ℝ) (h k : ℕ) : ℝ :=
  (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
    (Real.log T * Real.exp (4 * Cγ) * C * L) *
    ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
    (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
      (1 / 2 : ℝ)) *
    P ^ (9 / 4 : ℝ) * (X * Y) ^ (3 / 8 + ε)

/-- Boxwise Hughes--Young equation-(80) estimate.  Unlike a coarse bound
on the normalized dyadic factors, this keeps their square-root
denominators and therefore produces the source exponent `3/8` after the
shift sum. -/
theorem hughesYoungPointwiseDFIErrorMajorant_le_equation80Box
    {Cγ C L ε T P X Y : ℝ} {h k M N : ℕ}
    (hT : Real.exp 1 ≤ T) (hP : 1 ≤ P) (hX : 0 < X) (hY : 0 < Y)
    (hh : 0 < h) (hk : 0 < k)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (haX : (hughesYoungReducedLeft h k : ℝ) ≤ 2 * X)
    (hbY : (hughesYoungReducedRight h k : ℝ) ≤ 2 * Y)
    (hXY : X ≤ 4 * Y) (hYX : Y ≤ 4 * X) :
    hughesYoungPointwiseDFIErrorMajorant Cγ C L ε T P X Y h k M N ≤
      hughesYoungEquation80BoxErrorMajorant Cγ C L ε T P X Y h k := by
  let a : ℝ := hughesYoungReducedLeft h k
  let b : ℝ := hughesYoungReducedRight h k
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have ha : 0 < a := by
    dsimp only [a]
    exact_mod_cast hughesYoungReducedLeft_pos (k := k) hh
  have hb : 0 < b := by
    dsimp only [b]
    exact_mod_cast hughesYoungReducedRight_pos hh hk
  obtain ⟨hc0, hc1, _⟩ := hughesYoungSmallContour_spec hT
  have haRatio : 0 < a / X := div_pos ha hX
  have hbRatio : 0 < b / Y := div_pos hb hY
  have haRatioTwo : a / X ≤ 2 := (div_le_iff₀ hX).2 (by
    simpa only [a] using haX)
  have hbRatioTwo : b / Y ≤ 2 := (div_le_iff₀ hY).2 (by
    simpa only [b] using hbY)
  have haPow := rpow_half_add_le_two_mul_rpow_half
    haRatio haRatioTwo hc0.le hc1
  have hbPow := rpow_half_add_le_two_mul_rpow_half
    hbRatio hbRatioTwo hc0.le hc1
  have hRatio :
      (a / X) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
          (b / Y) ^ ((1 / 2 : ℝ) + hughesYoungSmallContour T) ≤
        4 * (a * b) ^ (1 / 2 : ℝ) *
          (X * Y) ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ (2 * (a / X) ^ (1 / 2 : ℝ)) *
          (2 * (b / Y) ^ (1 / 2 : ℝ)) := by gcongr
      _ = 4 * ((a / X) ^ (1 / 2 : ℝ) *
          (b / Y) ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by
        rw [mul_div_rpow_half_eq_mul_rpow_mul_product_rpow_neg_half
          ha hb hX hY]
        ring
  have hStatic := norm_hughesYoungLocalizedStaticScalar_le_coefficients
    (T := T) hh hk
  have hCard := cast_card_hughesYoungNearShifts_le_two_mul_div
    (T := T) (P := P) (X := X) (Y := Y)
    (a := hughesYoungReducedLeft h k) (b := hughesYoungReducedRight h k)
    (M := M) (N := N) hT0 hP0.le hY
  have hTCard :
      T * ((hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
        M N).card : ℝ) ≤ 2 * P * Y := by
    calc
      T * ((hughesYoungNearShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N).card : ℝ) ≤ T * (2 * P * Y / T) := by gcongr
      _ = 2 * P * Y := by field_simp
  have hScale := y_mul_sum_rpow_quarter_mul_product_rpow_le
    hX hY hXY hYX (ε := ε)
  have hXY0 : 0 < X * Y := mul_pos hX hY
  have habCast :
      (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ)) =
        a * b := by
    dsimp only [a, b]
    push_cast
    rfl
  have hPpow : P * P ^ (5 / 4 : ℝ) = P ^ (9 / 4 : ℝ) := by
    calc
      P * P ^ (5 / 4 : ℝ) = P ^ (1 : ℝ) * P ^ (5 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = P ^ ((1 : ℝ) + 5 / 4) := (Real.rpow_add hP0 1 (5 / 4)).symm
      _ = _ := congrArg (fun z : ℝ => P ^ z) (by norm_num)
  have hXYpow :
      (X * Y) ^ (-(1 / 2 : ℝ)) * (X * Y) ^ (1 / 4 + ε) =
        (X * Y) ^ (-(1 / 4 : ℝ) + ε) := by
    rw [← Real.rpow_add hXY0]
    congr 1
    ring
  unfold hughesYoungPointwiseDFIErrorMajorant
    hughesYoungEquation80BoxErrorMajorant dfiTheorem1ErrorScale
  simp only [a, b] at hRatio
  rw [habCast]
  calc
    (T * (Real.log T * Real.exp (4 * Cγ) *
        ((hughesYoungReducedLeft h k : ℝ) / X) ^
          ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
        ((hughesYoungReducedRight h k : ℝ) / Y) ^
          ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
        (((hughesYoungNearShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N).card : ℝ) *
          (‖hughesYoungLocalizedStaticScalar T h k‖ *
            (C * (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
              (X * Y) ^ (1 / 4 + ε)))))) * L ≤
      (Real.log T * Real.exp (4 * Cγ) * L) *
        (4 * ((hughesYoungReducedLeft h k : ℝ) *
          hughesYoungReducedRight h k) ^ (1 / 2 : ℝ) *
          (X * Y) ^ (-(1 / 2 : ℝ))) *
        (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖) *
        C * (2 * P * Y) *
        (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (1 / 4 + ε)) := by
        calc
          _ = (Real.log T * Real.exp (4 * Cγ) * L) *
              (((hughesYoungReducedLeft h k : ℝ) / X) ^
                ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
              ((hughesYoungReducedRight h k : ℝ) / Y) ^
                ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
              ‖hughesYoungLocalizedStaticScalar T h k‖ * C *
              (T * ((hughesYoungNearShifts T P X Y
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
                M N).card : ℝ)) *
              (P ^ (5 / 4 : ℝ) * (X + Y) ^ (1 / 4 : ℝ) *
                (X * Y) ^ (1 / 4 + ε)) := by ring
          _ ≤ _ := by gcongr
    _ = (8 * (Real.log T * Real.exp (4 * Cγ) * C * L) *
          ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (((hughesYoungReducedLeft h k : ℝ) *
            hughesYoungReducedRight h k) ^ (1 / 2 : ℝ)) *
          (P * P ^ (5 / 4 : ℝ))) *
        (Y * (X + Y) ^ (1 / 4 : ℝ) *
          ((X * Y) ^ (-(1 / 2 : ℝ)) *
            (X * Y) ^ (1 / 4 + ε))) := by ring
    _ = (8 * (Real.log T * Real.exp (4 * Cγ) * C * L) *
          ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (((hughesYoungReducedLeft h k : ℝ) *
            hughesYoungReducedRight h k) ^ (1 / 2 : ℝ)) *
          P ^ (9 / 4 : ℝ)) *
        (Y * (X + Y) ^ (1 / 4 : ℝ) *
          (X * Y) ^ (-(1 / 4 : ℝ) + ε)) := by
      rw [hPpow, hXYpow]
    _ ≤ (8 * (Real.log T * Real.exp (4 * Cγ) * C * L) *
          ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (((hughesYoungReducedLeft h k : ℝ) *
            hughesYoungReducedRight h k) ^ (1 / 2 : ℝ)) *
          P ^ (9 / 4 : ℝ)) *
        ((2 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
          (X * Y) ^ (3 / 8 + ε)) := by
      gcongr
    _ = _ := by ring

/-- The finite sum of the exact DFI error majorants over the concrete
large-DFI active family. -/
noncomputable def hughesYoungActiveLargeDFIErrorMajorant
    (Cγ C L ε T P : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungPointwiseDFIErrorMajorant Cγ C L ε T P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The full concrete large-box discrepancy consumes the exact signed DFI
Theorem-1 error box by box.  This theorem contains no central-term
majorant. -/
theorem exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T P : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 1 ≤ P →
      ‖hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K‖ ≤
        hughesYoungActiveLargeDFIErrorMajorant Cγ C L ε T P R K := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hbox⟩ :=
    exists_uniform_norm_hughesYoungNearPointwiseDFIDiscrepancyBox
      ε hε0 hε4
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T P R K hT hP
  classical
  unfold hughesYoungActiveLargeDFIPointwiseDiscrepancy
    hughesYoungActiveLargeDFIErrorMajorant
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            hughesYoungNearPointwiseDFIDiscrepancyBox T
              (hughesYoungSmallContour T) (T / 8) P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
            ‖hughesYoungNearPointwiseDFIDiscrepancyBox T
              (hughesYoungSmallContour T) (T / 8) P
              (hughesYoungFullDyadicScale ij.1)
              (hughesYoungFullDyadicScale ij.2) h k
              (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun h _hh =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk =>
            norm_sum_le _ _))
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
      have hp := (Finset.mem_filter.mp hij).2
      have hi : 0 < ij.1 := hp.1
      have hj : 0 < ij.2 := hp.2.1
      have hX : 1 ≤ hughesYoungFullDyadicScale ij.1 := by
        obtain ⟨i, hiEq⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        rw [hiEq]
        simpa only [Nat.succ_eq_add_one] using
          one_le_hughesYoungFullDyadicScale_succ i
      have hY : 1 ≤ hughesYoungFullDyadicScale ij.2 := by
        obtain ⟨j, hjEq⟩ :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
        rw [hjEq]
        simpa only [Nat.succ_eq_add_one] using
          one_le_hughesYoungFullDyadicScale_succ j
      have hM :
          2 * hughesYoungFullDyadicScale ij.1 /
              (hughesYoungReducedLeft h k : ℝ) ≤
            (hughesYoungFullDyadicBound ij.1 : ℝ) :=
        two_mul_fullDyadicScale_div_le_bound
          (a := hughesYoungReducedLeft h k) (i := ij.1)
          (hughesYoungReducedLeft_pos (k := k) hh)
      have hN :
          2 * hughesYoungFullDyadicScale ij.2 /
              (hughesYoungReducedRight h k : ℝ) ≤
            (hughesYoungFullDyadicBound ij.2 : ℝ) :=
        two_mul_fullDyadicScale_div_le_bound
          (a := hughesYoungReducedRight h k) (i := ij.2)
          (hughesYoungReducedRight_pos hh hk)
      have hlocal := hbox hT hX hY hh hk hP hp.2.2.2.2.1 hM hN
        hp.2.2.1 hp.2.2.2.1
      simpa only [hughesYoungPointwiseDFIErrorMajorant] using hlocal

/-- Sum of the explicit Hughes--Young equation-(80) box errors over the
concrete large/comparable DFI family. -/
noncomputable def hughesYoungActiveLargeDFIEquation80ErrorMajorant
    (Cγ C L ε T P : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungEquation80BoxErrorMajorant Cγ C L ε T P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k

/-- The exact pointwise DFI discrepancy is bounded by the source exponent
from Hughes--Young (80), summed over precisely the boxes on which (78)
applies. -/
theorem exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le_equation80
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ Cγ C L : ℝ, 0 < Cγ ∧ 0 < C ∧ 0 < L ∧
      ∀ {T P : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 1 ≤ P →
      ‖hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K‖ ≤
        hughesYoungActiveLargeDFIEquation80ErrorMajorant
          Cγ C L ε T P R K := by
  obtain ⟨Cγ, C, L, hCγ, hC, hL, hraw⟩ :=
    exists_norm_hughesYoungActiveLargeDFIPointwiseDiscrepancy_le
      ε hε0 hε4
  refine ⟨Cγ, C, L, hCγ, hC, hL, ?_⟩
  intro T P R K hT hP
  refine (hraw hT hP).trans ?_
  classical
  unfold hughesYoungActiveLargeDFIErrorMajorant
    hughesYoungActiveLargeDFIEquation80ErrorMajorant
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
  have hp := (Finset.mem_filter.mp hij).2
  have hi : 0 < ij.1 := hp.1
  have hj : 0 < ij.2 := hp.2.1
  have hX : 0 < hughesYoungFullDyadicScale ij.1 :=
    hughesYoungFullDyadicScale_pos ij.1
  have hY : 0 < hughesYoungFullDyadicScale ij.2 :=
    hughesYoungFullDyadicScale_pos ij.2
  exact hughesYoungPointwiseDFIErrorMajorant_le_equation80Box
    hT hP hX hY hh hk hC.le hL.le
    hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2

/-- Reduced mollifier coordinates contribute at most one full detector
index after taking the square root. -/
theorem reduced_product_rpow_half_le
    {h k ell : ℕ} (hh : h ≤ ell) (hk : k ≤ ell) :
    (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
      (1 / 2 : ℝ)) ≤ ell := by
  have ha : hughesYoungReducedLeft h k ≤ ell :=
    (hughesYoungReducedLeft_le h k).trans hh
  have hb : hughesYoungReducedRight h k ≤ ell :=
    (hughesYoungReducedRight_le h k).trans hk
  have hab : hughesYoungReducedLeft h k * hughesYoungReducedRight h k ≤
      ell * ell := Nat.mul_le_mul ha hb
  have habR :
      ((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ≤
        (ell : ℝ) ^ 2 := by
    have hab' : hughesYoungReducedLeft h k * hughesYoungReducedRight h k ≤
        ell ^ 2 := by simpa only [pow_two] using hab
    exact_mod_cast hab'
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt
        ((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ≤
      Real.sqrt ((ell : ℝ) ^ 2) := Real.sqrt_le_sqrt habR
    _ = (ell : ℝ) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg ell)]

/-- Finite global form of the equation-(80) error calculation.  All three
finite cardinalities are exposed, so the later asymptotic proof only has to
insert the concrete detector, conductor, and logarithmic-depth bounds. -/
theorem hughesYoungActiveLargeDFIEquation80ErrorMajorant_le
    {Cγ C L ε T P A : ℝ} {R K : ℕ}
    (hT : 1 ≤ T) (hP : 0 ≤ P) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hcoeff : ∀ n ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖shortMobiusSquareCoeff T n‖ ≤ A) :
    hughesYoungActiveLargeDFIEquation80ErrorMajorant
        Cγ C L ε T P R K ≤
      ((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2) *
        (((K + 2 : ℕ) : ℝ) ^ 2) *
        ((16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
          (Real.log T * Real.exp (4 * Cγ) * C * L) *
          A ^ 2 * (((detectorCutoff T) ^ 2 : ℕ) : ℝ) *
          P ^ (9 / 4 : ℝ) *
          (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 * (R : ℝ)) ^
            (3 / 8 + ε))) := by
  classical
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℝ :=
    (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
      (Real.log T * Real.exp (4 * Cγ) * C * L) *
      A ^ 2 * (ell : ℝ) * P ^ (9 / 4 : ℝ) *
      ((((ell : ℝ) ^ 2 * (R : ℝ)) ^ (3 / 8 + ε)))
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
    positivity
  have hbox : ∀ h ∈ Finset.Icc 1 ell, ∀ k ∈ Finset.Icc 1 ell,
      ∀ ij ∈ hughesYoungActiveLargeDFIBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      hughesYoungEquation80BoxErrorMajorant Cγ C L ε T P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k ≤ B := by
    intro h hhmem k hkmem ij hij
    have hijActive := (Finset.mem_filter.mp hij).1
    have hprod := (Finset.mem_filter.mp hijActive).2
    have hhUpper : h ≤ ell := (Finset.mem_Icc.mp hhmem).2
    have hkUpper : k ≤ ell := (Finset.mem_Icc.mp hkmem).2
    have hred := reduced_product_rpow_half_le hhUpper hkUpper
    have habNat : hughesYoungReducedLeft h k * hughesYoungReducedRight h k ≤
        ell * ell := Nat.mul_le_mul
          ((hughesYoungReducedLeft_le h k).trans hhUpper)
          ((hughesYoungReducedRight_le h k).trans hkUpper)
    have habR :
        ((hughesYoungReducedLeft h k : ℝ) *
          hughesYoungReducedRight h k) * (R : ℝ) ≤
            (ell : ℝ) ^ 2 * (R : ℝ) := by
      have habCast :
          (hughesYoungReducedLeft h k : ℝ) *
              hughesYoungReducedRight h k ≤ (ell : ℝ) ^ 2 := by
        have habNat' :
            hughesYoungReducedLeft h k * hughesYoungReducedRight h k ≤
              ell ^ 2 := by simpa only [pow_two] using habNat
        exact_mod_cast habNat'
      gcongr
    have hscaleProd :
        hughesYoungFullDyadicScale ij.1 *
            hughesYoungFullDyadicScale ij.2 ≤
          (ell : ℝ) ^ 2 * (R : ℝ) := by
      exact hprod.trans (by
        simpa only [Nat.cast_mul, pow_two] using habR)
    have hscalePow :
        (hughesYoungFullDyadicScale ij.1 *
          hughesYoungFullDyadicScale ij.2) ^ (3 / 8 + ε) ≤
          (((ell : ℝ) ^ 2 * (R : ℝ)) ^ (3 / 8 + ε)) := by
      exact Real.rpow_le_rpow
        (mul_nonneg (hughesYoungFullDyadicScale_pos ij.1).le
          (hughesYoungFullDyadicScale_pos ij.2).le)
        hscaleProd (by linarith)
    unfold hughesYoungEquation80BoxErrorMajorant
    dsimp only [B, ell]
    have hcoeffPair :
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ ≤
          A * A := by
      exact mul_le_mul (hcoeff h (by simpa only [ell] using hhmem))
        (hcoeff k (by simpa only [ell] using hkmem)) (norm_nonneg _) hA
    have hfront : 0 ≤
        (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
          (Real.log T * Real.exp (4 * Cγ) * C * L) := by
      have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
      positivity
    let D : ℝ := (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
      (Real.log T * Real.exp (4 * Cγ) * C * L)
    have hD : 0 ≤ D := by simpa only [D] using hfront
    have hred0 : 0 ≤
        (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
          (1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have hell0 : (0 : ℝ) ≤ ((detectorCutoff T) ^ 2 : ℕ) := by positivity
    have hPpow0 : 0 ≤ P ^ (9 / 4 : ℝ) := Real.rpow_nonneg hP _
    have hboxPow0 : 0 ≤
        (hughesYoungFullDyadicScale ij.1 *
          hughesYoungFullDyadicScale ij.2) ^ (3 / 8 + ε) :=
      Real.rpow_nonneg
        (mul_nonneg (hughesYoungFullDyadicScale_pos ij.1).le
          (hughesYoungFullDyadicScale_pos ij.2).le) _
    calc
      _ = D *
          (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖) *
          (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
            (1 / 2 : ℝ)) * P ^ (9 / 4 : ℝ) *
          (hughesYoungFullDyadicScale ij.1 *
            hughesYoungFullDyadicScale ij.2) ^ (3 / 8 + ε) := by
        dsimp only [D]
        ring
      _ ≤ D * (A * A) *
          (((hughesYoungReducedLeft h k * hughesYoungReducedRight h k : ℕ) : ℝ) ^
            (1 / 2 : ℝ)) * P ^ (9 / 4 : ℝ) *
          (hughesYoungFullDyadicScale ij.1 *
            hughesYoungFullDyadicScale ij.2) ^ (3 / 8 + ε) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoeffPair hD) hred0) hPpow0)
          hboxPow0
      _ ≤ D * (A * A) * (((detectorCutoff T) ^ 2 : ℕ) : ℝ) *
          P ^ (9 / 4 : ℝ) *
          (hughesYoungFullDyadicScale ij.1 *
            hughesYoungFullDyadicScale ij.2) ^ (3 / 8 + ε) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hred
              (mul_nonneg hD (mul_nonneg hA hA))) hPpow0) hboxPow0
      _ ≤ (16 * (4 : ℝ) ^ (1 / 4 : ℝ)) *
          (Real.log T * Real.exp (4 * Cγ) * C * L) *
          A * A * (((detectorCutoff T) ^ 2 : ℕ) : ℝ) *
          P ^ (9 / 4 : ℝ) *
          (((((detectorCutoff T) ^ 2 : ℕ) : ℝ) ^ 2 * (R : ℝ)) ^
            (3 / 8 + ε)) := by
        dsimp only [D]
        convert mul_le_mul_of_nonneg_left hscalePow
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg hfront (mul_nonneg hA hA)) hell0) hPpow0) using 1
        all_goals ring
      _ = _ := by ring
  unfold hughesYoungActiveLargeDFIEquation80ErrorMajorant
  change (∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
      ∑ ij ∈ hughesYoungActiveLargeDFIBoxes P
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungEquation80BoxErrorMajorant Cγ C L ε T P
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k) ≤ _
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ _ij ∈ hughesYoungActiveLargeDFIBoxes P
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          B := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      exact Finset.sum_le_sum (hbox h hhmem k hkmem)
    _ ≤ ∑ _h ∈ Finset.Icc 1 ell, ∑ _k ∈ Finset.Icc 1 ell,
        (((K + 2 : ℕ) : ℝ) ^ 2) * B := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro k _hk
      rw [Finset.sum_const, nsmul_eq_mul]
      have hfilter :
          (hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            R K).card ≤
            (hughesYoungActiveDyadicBoxes
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              R K).card := by
        unfold hughesYoungActiveLargeDFIBoxes
        exact Finset.card_filter_le _ _
      have hcardNat := hfilter.trans
        (card_hughesYoungActiveDyadicBoxes_le
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
      have hcard :
          ((hughesYoungActiveLargeDFIBoxes P
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            R K).card : ℝ) ≤ (((K + 2) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hcardNat
      have hmul := mul_le_mul_of_nonneg_right hcard hB
      push_cast at hmul
      simpa only [Nat.cast_add, Nat.cast_ofNat] using hmul
    _ = (((Finset.Icc 1 ell).card : ℝ) ^ 2) *
        ((((K + 2 : ℕ) : ℝ) ^ 2) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ ((ell : ℝ) ^ 2) * ((((K + 2 : ℕ) : ℝ) ^ 2) * B) := by
      have hcardNat : (Finset.Icc 1 ell).card ≤ ell := by
        simp
      have hcard : ((Finset.Icc 1 ell).card : ℝ) ≤ ell := by
        exact_mod_cast hcardNat
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hcard 2)
        (mul_nonneg (by positivity) hB)
    _ = _ := by
      dsimp only [B, ell]
      ring

end RiemannZeta.GuthMaynard
