import RiemannZeta.GuthMaynard.HughesYoungSmallBox

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Optimized large/small scale split for one Hughes--Young box
-/

/-- The large-box majorant after cancelling the positive equation-(65)
prefactor. -/
noncomputable def hughesYoungLargeBoxMajorant
    (Cγnear Cnear Lnear : ℝ) (Cw : ℕ → ℝ) (Dfar Lfar : ℝ)
    (j : ℕ) (T P X Y ε : ℝ) (h k M N : ℕ) : ℝ :=
  hughesYoungNearBoxMajorant Cγnear Cnear Lnear T P X Y ε h k M N +
    (P / (5 * T)) ^ (-(j : ℤ)) *
      hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N

theorem norm_hughesYoungLocalizedOffDiagonalBox_le_largeMajorant
    {Cγnear Cnear Lnear Dfar Lfar T P X Y ε : ℝ}
    {Cw : ℕ → ℝ} {j h k M N : ℕ}
    (hT : 0 < T) (hP : 0 < P)
    (hscaled :
      (P / (5 * T)) ^ j *
          ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
        (P / (5 * T)) ^ j *
            hughesYoungNearBoxMajorant Cγnear Cnear Lnear
              T P X Y ε h k M N +
          hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N) :
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungLargeBoxMajorant Cγnear Cnear Lnear Cw Dfar Lfar
        j T P X Y ε h k M N := by
  let q : ℝ := P / (5 * T)
  have hq : 0 < q := div_pos hP (mul_pos (by norm_num) hT)
  have hqj : 0 < q ^ j := pow_pos hq j
  have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt (inv_pos.mpr hqj))
  have hcancel : (q ^ j)⁻¹ * q ^ j = 1 := inv_mul_cancel₀ hqj.ne'
  have hzinv : q ^ (-(j : ℤ)) = (q ^ j)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  unfold hughesYoungLargeBoxMajorant
  change ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
      hughesYoungNearBoxMajorant Cγnear Cnear Lnear T P X Y ε h k M N +
        q ^ (-(j : ℤ)) *
          hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N
  rw [hzinv]
  calc
    ‖hughesYoungLocalizedOffDiagonalBox T
        (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ =
        (q ^ j)⁻¹ * (q ^ j *
          ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8) X Y h k M N‖) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (q ^ j)⁻¹ *
        (q ^ j * hughesYoungNearBoxMajorant Cγnear Cnear Lnear
            T P X Y ε h k M N +
          hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N) := hmul
    _ = hughesYoungNearBoxMajorant Cγnear Cnear Lnear
          T P X Y ε h k M N +
        (q ^ j)⁻¹ *
          hughesYoungFarBoxMajorant Cw Dfar Lfar j T X Y ε h k M N := by
      field_simp [hq.ne']

/-- Every physical dyadic box is routed either to native DFI with the
optimized scale, or to the arbitrary-order equation-(65) estimate. -/
theorem exists_hughesYoungLocalizedOffDiagonalBox_scale_split
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) (j : ℕ) :
    ∃ Cγnear Cnear Lnear Cγfar Dfar Lfar Cγsmall Dsmall Lsmall : ℝ,
      0 < Cγnear ∧ 0 < Cnear ∧ 0 < Lnear ∧
      0 < Cγfar ∧ 0 < Dfar ∧ 0 < Lfar ∧
      0 < Cγsmall ∧ 0 < Dsmall ∧ 0 < Lsmall ∧
      ∃ CwFar CwSmall : ℕ → ℝ,
        (∀ i, 0 < CwFar i) ∧ (∀ i, 0 < CwSmall i) ∧
      ∀ {T X Y P : ℝ} {h k M N : ℕ},
      Real.exp 1 ≤ T → 16 ≤ T →
      1 ≤ X → 1 ≤ Y → 0 < h → 0 < k →
      1 ≤ P → P ≤ T →
      2 * X / hughesYoungReducedLeft h k ≤ M →
      2 * Y / hughesYoungReducedRight h k ≤ N →
      ((hughesYoungReducedLeft h k : ℕ) : ℝ) ≤ 2 * X →
      ((hughesYoungReducedRight h k : ℕ) : ℝ) ≤ 2 * Y →
      4 * Cγfar * hughesYoungSmallContour T ≤ 1 →
      4 * Cγsmall * hughesYoungSmallContour T ≤ 1 →
      (64 ≤ hughesYoungDFIOptimalU P X Y ∧
        ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
          hughesYoungLargeBoxMajorant Cγnear Cnear Lnear CwFar Dfar Lfar
            j T P X Y ε h k M N) ∨
      (hughesYoungDFIOptimalU P X Y < 64 ∧
        ‖hughesYoungLocalizedOffDiagonalBox T
            (hughesYoungSmallContour T) (T / 8) X Y h k M N‖ ≤
          hughesYoungSmallBoxMajorant CwSmall Dsmall Lsmall
            j T X Y ε h k M N) := by
  obtain ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
      hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
      CwFar, hCwFar, hlarge⟩ :=
    exists_hughesYoungLocalizedOffDiagonalBox_full_consumer ε hε0 hε4 j
  obtain ⟨Cγsmall, Dsmall, Lsmall, hCγsmall, hDsmall, hLsmall,
      CwSmall, hCwSmall, hsmallBox⟩ :=
    exists_hughesYoungLocalizedOffDiagonalBox_smallScale_scaled_bound ε hε0 j
  refine ⟨Cγnear, Cnear, Lnear, Cγfar, Dfar, Lfar,
    Cγsmall, Dsmall, Lsmall,
    hCγnear, hCnear, hLnear, hCγfar, hDfar, hLfar,
    hCγsmall, hDsmall, hLsmall, CwFar, CwSmall,
    hCwFar, hCwSmall, ?_⟩
  intro T X Y P h k M N hTexp hT16 hX hY hh hk hP hPT hM hN haX hbY
    hfarSmall hsmallSmall
  have hT0 : 0 < T := by linarith
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  by_cases hU : 64 ≤ hughesYoungDFIOptimalU P X Y
  · left
    refine ⟨hU, ?_⟩
    obtain ⟨hscale, hQ, hUQ, hQsq⟩ :=
      hughesYoungDFIOptimalScale_spec hP0
        (lt_of_lt_of_le zero_lt_one hX) (lt_of_lt_of_le zero_lt_one hY) hU
    have hscaled := hlarge (T := T) (H := T / 8) (X := X) (Y := Y)
      (P := P) (U := hughesYoungDFIOptimalU P X Y)
      (Q := hughesYoungDFIOptimalQ P X Y) (h := h) (k := k)
      (M := M) (N := N) hTexp hT16 (by positivity) le_rfl hX hY hh hk
      hP hPT hscale hQ hUQ hQsq hM hN haX hbY hfarSmall
    exact norm_hughesYoungLocalizedOffDiagonalBox_le_largeMajorant
      hT0 hP0 hscaled
  · right
    refine ⟨hughesYoungDFIOptimalU_lt_sixtyFour_of_not_large hU, ?_⟩
    have hscaled := hsmallBox (M := M) (N := N) hTexp hT16 hsmallSmall
      (by positivity) le_rfl (lt_of_lt_of_le zero_lt_one hX) hY hh hk
    exact norm_hughesYoungLocalizedOffDiagonalBox_le_smallMajorant_of_scaled
      hT0 (lt_of_lt_of_le zero_lt_one hY) hscaled

end RiemannZeta.GuthMaynard
