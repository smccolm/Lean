import RiemannZeta.GuthMaynard.HughesYoungFarShift

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Finite-box Hughes--Young consumer

This module reconnects the near- and far-shift estimates to the actual
localized off-diagonal term obtained from the four-index AFE expansion.
-/

/-- The original-coordinate source weight on the dyadic box which becomes
`hughesYoungGCDReducedIntegratedBoxWeight` after removing `gcd(h,k)`. -/
noncomputable def hughesYoungPreReducedIntegratedBoxWeight
    (T c H X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  let d : ℝ := hughesYoungCommonDivisor h k
  (hughesYoungDyadicCutoffAt (d * X) x : ℂ) *
    (hughesYoungDyadicCutoffAt (d * Y) y : ℂ) *
    hughesYoungIntegratedSourceWeight T c H h k x y

/-- One actual finite localized off-diagonal box before gcd reduction. -/
noncomputable def hughesYoungLocalizedOffDiagonalBox
    (T c H X Y : ℝ) (h k M N : ℕ) : ℂ :=
  finiteQuadraticDivisorOffDiagonal h k M N
    (fun x y => hughesYoungPreReducedIntegratedBoxWeight
      T c H X Y h k x y)

theorem hughesYoungGCDScaledWeight_preReduced_eq
    (T c H X Y : ℝ) (h k : ℕ) (x y : ℝ) :
    hughesYoungGCDScaledWeight h k
        (hughesYoungPreReducedIntegratedBoxWeight T c H X Y h k) x y =
      hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k x y := by
  rfl

/-- Exact source-entry identity: the literal off-diagonal box is the disjoint
sum of the DFI near family and the equation-(65) complementary family. -/
theorem hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    (T c H P X Y : ℝ) {h k M N : ℕ} (hh : 0 < h) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N =
      (∑ r ∈ hughesYoungNearShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r) +
      (∑ r ∈ hughesYoungFarShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r) := by
  let F : ℝ → ℝ → ℂ :=
    hughesYoungPreReducedIntegratedBoxWeight T c H X Y h k
  let G : ℝ → ℝ → ℂ :=
    hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k
  have hreduce : hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N =
      ∑ r ∈ hughesYoungShiftInterval
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        if r = 0 then 0 else
          dfiDyadicShiftedDivisorSum G
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r := by
    unfold hughesYoungLocalizedOffDiagonalBox
    rw [finiteQuadraticDivisorOffDiagonal_eq_sum_gcdReduced_dfiShifts hh F]
    apply Finset.sum_congr rfl
    intro r _hr
    by_cases hr0 : r = 0
    · simp [hr0]
    · simp only [hr0, if_false]
      congr 1
  rw [hreduce]
  exact sum_shiftInterval_eq_near_add_far
    (fun r => dfiDyadicShiftedDivisorSum G
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r)
    T P X Y (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N

/-- Norm consequence of the exact near/far source partition. -/
theorem norm_hughesYoungLocalizedOffDiagonalBox_le_near_add_far
    (T c H P X Y : ℝ) {h k M N : ℕ} (hh : 0 < h) :
    ‖hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N‖ ≤
      ‖∑ r ∈ hughesYoungNearShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r‖ +
      ‖∑ r ∈ hughesYoungFarShifts T P X Y
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
        dfiDyadicShiftedDivisorSum
          (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
          M N r‖ := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far T c H P X Y hh]
  exact norm_add_le _ _

/-- The exact near-range majorant delivered by native DFI Theorem 1. -/
noncomputable def hughesYoungNearBoxMajorant
    (Cγ C L T P X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  (T * (Real.log T * Real.exp (4 * Cγ) *
    ((hughesYoungReducedLeft h k : ℝ) / X) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
    ((hughesYoungReducedRight h k : ℝ) / Y) ^
      ((1 / 2 : ℝ) + hughesYoungSmallContour T)) *
    hughesYoungIntegratedDFIArithmeticTotal C T P X Y ε h k
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
      (hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N)) * L

/-- The complete far-range majorant after equation (65), divisor summation,
and the Gaussian ordinate integral. -/
noncomputable def hughesYoungFarBoxMajorant
    (Cw : ℕ → ℝ) (D L : ℝ) (j : ℕ)
    (T X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  (((15 * T / 4) * (hughesYoungSmallContour T)⁻¹ * Real.exp 100 *
      (6 * T) * hughesYoungHeightInputDerivativeConstant Cw j *
      ((T / 16)⁻¹) ^ j) * L) *
    (D * (M : ℝ) ^ (1 + ε) * (N : ℝ) ^ (1 + ε) *
      ‖hughesYoungLocalizedStaticScalar T h k‖ *
      (((hughesYoungReducedLeft h k : ℕ) : ℝ) / X) ^
        ((1 / 2 : ℝ) + hughesYoungSmallContour T) *
      (((hughesYoungReducedRight h k : ℕ) : ℝ) / Y) ^
        ((1 / 2 : ℝ) + hughesYoungSmallContour T))

/-- Full finite-box Hughes--Young/DFI consumer.  Its left side is the actual
localized AFE off-diagonal box; the right side contains only the explicit DFI
near majorant and the explicit equation-(65) far majorant. -/
theorem exists_hughesYoungLocalizedOffDiagonalBox_full_consumer
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) (j : ℕ) :
    ∃ Cγnear Cnear Lnear Cγfar Dfar Lfar : ℝ,
      0 < Cγnear ∧ 0 < Cnear ∧ 0 < Lnear ∧
      0 < Cγfar ∧ 0 < Dfar ∧ 0 < Lfar ∧
      ∃ Cw : ℕ → ℝ, (∀ i, 0 < Cw i) ∧
      ∀ {T H X Y P U Q : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T → 0 ≤ H → H ≤ T / 8 →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k → 1 ≤ P → P ≤ T →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      4 * Cγfar * hughesYoungSmallContour T ≤ 1 →
      (P / (5 * T)) ^ j *
          ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) H X Y h k M N‖ ≤
        (P / (5 * T)) ^ j *
          hughesYoungNearBoxMajorant Cγnear Cnear Lnear
            T P X Y ε h k M N +
        hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N := by
  obtain ⟨Cγnear, Cnear, Lnear, hCγnear, hCnear, hLnear, hnear⟩ :=
    exists_uniform_norm_hughesYoungNearShiftSource_full_dfi ε hε0 hε4
  obtain ⟨Cγfar, Dfar, Lfar, hCγfar, hDfar, hLfar, Cw, hCw, hfar⟩ :=
    exists_integrated_farShift_sum_full_bound ε hε0 j
  refine ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
    hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar, Cw, hCw, ?_⟩
  intro T H X Y P U Q h k M N hTexp hT16 hH hHT hX hY hh hk hP hPT
    hscale hQ hU hQsq hM hN haX hbY hsmall
  have hT0 : 0 < T := by linarith
  have hcSpec := hughesYoungSmallContour_spec hTexp
  obtain ⟨hc, hc1, _hcinv⟩ := hcSpec
  have hnearBound := hnear hTexp hH hX hY hh hk hP hscale hQ hU hQsq
    hM hN haX hbY
  have hfarBound := hfar (T := T) (c := hughesYoungSmallContour T) (H := H)
    (P := P) (X := X) (Y := Y) (h := h) (k := k)
    (a := hughesYoungReducedLeft h k) (b := hughesYoungReducedRight h k)
    (M := M) (N := N) hT16 hc hc1 hsmall hH hHT
    (lt_of_lt_of_le zero_lt_one hP) hPT
    (lt_of_lt_of_le zero_lt_one hX) (lt_of_lt_of_le zero_lt_one hY)
    hh hk (hughesYoungReducedLeft_pos hh)
    (hughesYoungReducedRight_pos hh hk)
  have hq : 0 ≤ (P / (5 * T)) ^ j := by positivity
  have hbox := norm_hughesYoungLocalizedOffDiagonalBox_le_near_add_far
    T (hughesYoungSmallContour T) H P X Y (h := h) (k := k)
      (M := M) (N := N) hh
  calc
    (P / (5 * T)) ^ j *
        ‖hughesYoungLocalizedOffDiagonalBox T
          (hughesYoungSmallContour T) H X Y h k M N‖ ≤
      (P / (5 * T)) ^ j *
        (‖∑ r ∈ hughesYoungNearShifts T P X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDReducedIntegratedBoxWeight T
              (hughesYoungSmallContour T) H X Y h k)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r‖ +
         ‖∑ r ∈ hughesYoungFarShifts T P X Y
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
          dfiDyadicShiftedDivisorSum
            (hughesYoungGCDReducedIntegratedBoxWeight T
              (hughesYoungSmallContour T) H X Y h k)
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
            M N r‖) := mul_le_mul_of_nonneg_left hbox hq
    _ = (P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungNearShifts T P X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungGCDReducedIntegratedBoxWeight T
                (hughesYoungSmallContour T) H X Y h k)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              M N r‖ +
        (P / (5 * T)) ^ j *
          ‖∑ r ∈ hughesYoungFarShifts T P X Y
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
            dfiDyadicShiftedDivisorSum
              (hughesYoungGCDReducedIntegratedBoxWeight T
                (hughesYoungSmallContour T) H X Y h k)
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k)
              M N r‖ := by ring
    _ ≤ (P / (5 * T)) ^ j *
          hughesYoungNearBoxMajorant Cγnear Cnear Lnear
            T P X Y ε h k M N +
          hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (by
          simpa only [hughesYoungNearBoxMajorant] using hnearBound) hq
      · simpa only [hughesYoungFarBoxMajorant] using hfarBound

end RiemannZeta.GuthMaynard
