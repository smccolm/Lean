import Tao2026.SylvesterSchurCentralTail
import Tao2026.SmoothNumberPrimeSum

namespace Tao2026

#check Real.le_sqrt
#check Real.le_sqrt_of_sq_le

theorem probe_baseline_log {H : ℕ} (hH : 4 ^ 101 ≤ H) :
    (H.primeCounting : ℝ) * Real.log (1024 * H) <
      (H : ℝ) * Real.log 1024 := by
  let X : ℝ := H
  let S : ℝ := Real.sqrt X
  let L : ℝ := Real.log X
  let C : ℝ := Real.log 1024
  have hHBig : 1_000_000 ≤ H := by
    exact (by norm_num : 1_000_000 ≤ 4 ^ 101).trans hH
  have hXPos : 0 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 0 < H)
  have hXOne : 1 < X := by
    dsimp [X]
    exact_mod_cast (by omega : 1 < H)
  have hLPos : 0 < L := by exact Real.log_pos hXOne
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog1024 : C = 10 * Real.log 2 := by
    dsimp [C]
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num]
    rw [Real.log_pow]
    norm_num
  have hCUpper : C < 7 := by
    rw [hlog1024]
    nlinarith [Real.log_two_lt_d9]
  have hCLower : (69 / 10 : ℝ) < C := by
    rw [hlog1024]
    nlinarith [Real.log_two_gt_d9]
  have hlogFourUpper : Real.log 4 < (7 / 5 : ℝ) := by
    rw [hlogFour]
    nlinarith [Real.log_two_lt_d9]
  have hXBound : (4 : ℝ) ^ 101 ≤ X := by
    dsimp [X]
    exact_mod_cast hH
  have hlogMono : Real.log ((4 : ℝ) ^ 101) ≤ L := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr hXPos
    · exact hXBound
  have hL : (140 : ℝ) < L := by
    have hpowLog : Real.log ((4 : ℝ) ^ 101) = 101 * Real.log 4 := by
      rw [Real.log_pow]
      norm_num
    rw [hpowLog, hlogFour] at hlogMono
    nlinarith [Real.log_two_gt_d9]
  have hSNonneg : 0 ≤ S := Real.sqrt_nonneg X
  have hSSq : S * S = X := Real.mul_self_sqrt hXPos.le
  have hSGe : (1000 : ℝ) ≤ S := by
    dsimp [S]
    apply Real.le_sqrt_of_sq_le
    dsimp [X]
    exact_mod_cast hHBig
  have hSLe : S ≤ X / 1000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)]
    nlinarith
  have hLogLe : L ≤ 2 * S := by
    have h := Real.log_le_rpow_div hXPos.le
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    dsimp [L, S, X]
    convert h using 1 <;> ring
  have hSL : S * L ≤ 2 * X := by nlinarith
  have hPrime := primeCounting_cast_le_chebyshevPrimeCountingMajorant
    (n := H) (by omega : 2 ≤ H)
  have hPrime' :
      (H.primeCounting : ℝ) ≤
        2 * Real.log 4 * X / L + S := by
    rw [chebyshevPrimeCountingMajorant,
      Real.log_sqrt (by exact_mod_cast (Nat.zero_le H))] at hPrime
    dsimp [X, S, L] at hPrime ⊢
    convert hPrime using 1 <;> field_simp
  have hA : Real.log (1024 * H) = L + C := by
    dsimp [L, C, X]
    rw [Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) hXPos.ne']
    ring
  rw [hA]
  have hANonneg : 0 ≤ L + C := by positivity
  have hpiA :
      (H.primeCounting : ℝ) * (L + C) ≤
        (2 * Real.log 4 * X / L + S) * (L + C) :=
    mul_le_mul_of_nonneg_right hPrime' hANonneg
  have hfirst :
      (2 * Real.log 4 * X / L) * (L + C) <
        (147 / 50 : ℝ) * X := by
    have hXC : X * C / L < X / 20 := by
      rw [div_lt_iff₀ hLPos, div_mul_eq_mul_div]
      have : C * 20 < L := by nlinarith
      nlinarith
    have hmain : 2 * Real.log 4 * X < (14 / 5 : ℝ) * X := by
      nlinarith
    have hcoeff : 2 * Real.log 4 < (14 / 5 : ℝ) := by nlinarith
    have hXCPos : 0 < X * C / L := by positivity
    calc
      (2 * Real.log 4 * X / L) * (L + C) =
          2 * Real.log 4 * X + 2 * Real.log 4 * (X * C / L) := by
        field_simp
      _ < (14 / 5 : ℝ) * X +
          (14 / 5 : ℝ) * (X * C / L) := by
        exact add_lt_add hmain (mul_lt_mul_of_pos_right hcoeff hXCPos)
      _ < (14 / 5 : ℝ) * X + (14 / 5 : ℝ) * (X / 20) := by
        exact add_lt_add_left
          (mul_lt_mul_of_pos_left hXC
            (by norm_num : (0 : ℝ) < 14 / 5)) _
      _ = (147 / 50 : ℝ) * X := by ring
  have hsqrtPart : S * (L + C) < (2007 / 1000 : ℝ) * X := by
    have hSC : S * C < 7 * (X / 1000) := by
      nlinarith
    nlinarith
  have htotal :
      (2 * Real.log 4 * X / L + S) * (L + C) <
        (4947 / 1000 : ℝ) * X := by
    nlinarith
  have htarget : (4947 / 1000 : ℝ) * X < X * C := by
    have : (0 : ℝ) < X := hXPos
    nlinarith
  exact hpiA.trans_lt (htotal.trans htarget)

end Tao2026
