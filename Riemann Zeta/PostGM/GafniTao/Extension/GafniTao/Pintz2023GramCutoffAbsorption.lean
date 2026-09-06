import GafniTao.Pintz2023Equation423Endpoint
import GafniTao.Pintz2023DetectorEventually
import GafniTao.PintzNearOneZetaSum

/-!
# Absorption of Pintz's explicit Gram shell counts

This file spends one strict epsilon only after the exact low and middle
shell estimates have been assembled.  The integer `clog`, ceiling, and
`log^2` cutoff are all bounded explicitly before little-oh is invoked.
-/

open Filter Topology
open RiemannZeta.GuthMaynard

namespace GafniTao

noncomputable section

/-- Eventually the binary shell count of `A` costs at most the displayed
multiple of `log A`. -/
theorem eventually_clog_two_le_two_inv_log_mul_log :
    ∀ᶠ A : ℕ in atTop,
      (Nat.clog 2 A : ℝ) ≤
        2 * (Real.log 2)⁻¹ * Real.log A := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNatTop
  filter_upwards [eventually_ge_atTop 1,
    hlogTop.eventually (eventually_ge_atTop 1)] with A hA hlog
  have hraw := natCast_clog_two_le_one_add_log A hA
  have hone : 1 ≤ Real.log A := hlog
  calc
    (Nat.clog 2 A : ℝ) ≤ 1 + Real.log A / Real.log 2 := hraw
    _ ≤ (Real.log 2)⁻¹ * Real.log A +
        (Real.log 2)⁻¹ * Real.log A := by
      have hlogTwoLeOne : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
      have hinvOne : 1 ≤ (Real.log 2)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ hlogTwo]
        simpa using hlogTwoLeOne
      have honeTerm : 1 ≤ (Real.log 2)⁻¹ * Real.log A := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (Real.log 2)⁻¹ * Real.log A :=
            mul_le_mul hinvOne hone (by norm_num) (by linarith)
      rw [div_eq_mul_inv]
      rw [mul_comm (Real.log A) (Real.log 2)⁻¹]
      linarith
    _ = 2 * (Real.log 2)⁻¹ * Real.log A := by ring

/-- The terminal cutoff has only logarithmically many binary shells. -/
theorem eventually_clog_two_gramCutoff_le_eight_inv_log_mul_log :
    ∀ᶠ A : ℕ in atTop,
      (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) ≤
        8 * (Real.log 2)⁻¹ * Real.log A := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNatTop
  have hlogSq := hNatTop.eventually
    (eventually_log_sq_le_rpow (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop 4,
    hlogTop.eventually (eventually_ge_atTop 1), hlogSq] with
      A hA hlog hlogSqA
  have hAOne : 1 ≤ A := by omega
  have hlogOne : 1 ≤ Real.log A := hlog
  have hMOne : 1 ≤ pintz2023GramCutoff A :=
    hAOne.trans (le_pintz2023GramCutoff hlogOne)
  have hMUpperRaw := pintz2023GramCutoff_cast_le_four_mul_log_sq hlogOne
  have hMUpper : (pintz2023GramCutoff A : ℝ) ≤ (A : ℝ) ^ 3 := by
    calc
      (pintz2023GramCutoff A : ℝ) ≤
          4 * (A : ℝ) * (Real.log A) ^ 2 := hMUpperRaw
      _ ≤ 4 * (A : ℝ) * (A : ℝ) := by
        gcongr
        simpa only [Real.rpow_one] using hlogSqA
      _ ≤ (A : ℝ) ^ 3 := by
        have hAReal : (4 : ℝ) ≤ A := by exact_mod_cast hA
        nlinarith [sq_nonneg ((A : ℝ) - 4)]
  have hMPos : (0 : ℝ) < pintz2023GramCutoff A := by
    exact_mod_cast (show 0 < pintz2023GramCutoff A by omega)
  have hlogM : Real.log (pintz2023GramCutoff A : ℝ) ≤
      3 * Real.log A := by
    calc
      Real.log (pintz2023GramCutoff A : ℝ) ≤ Real.log ((A : ℝ) ^ 3) :=
        Real.log_le_log hMPos hMUpper
      _ = 3 * Real.log A := by
        rw [Real.log_pow]
        norm_num
  have hraw := natCast_clog_two_le_one_add_log
    (pintz2023GramCutoff A) hMOne
  have hinvOne : 1 ≤ (Real.log 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hlogTwo]
    linarith [Real.log_two_lt_d9]
  have hlogNonneg : 0 ≤ Real.log A := zero_le_one.trans hlogOne
  calc
    (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) ≤
        1 + Real.log (pintz2023GramCutoff A : ℝ) / Real.log 2 := hraw
    _ ≤ 1 + (3 * Real.log A) / Real.log 2 := by gcongr
    _ ≤ (Real.log 2)⁻¹ * Real.log A +
        3 * (Real.log 2)⁻¹ * Real.log A := by
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_right hinvOne hlogNonneg]
    _ ≤ 8 * (Real.log 2)⁻¹ * Real.log A := by
      have hterm : 0 ≤ (Real.log 2)⁻¹ * Real.log A := by positivity
      nlinarith

/-- One epsilon absorbs the exact low-shell count. -/
theorem eventually_pintz2023_low_shell_endpoint_absorbed
    {C eta epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ A : ℕ in atTop,
      (Nat.clog 2 A : ℝ) *
          (2 * C * (A : ℝ) ^ (4 * eta) *
            (A : ℝ) ^ (-3 * epsilon)) ≤
        (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
  let D : ℝ := 4 * C * (Real.log 2)⁻¹
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hsmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := D) (p := 1) (q := epsilon) (b := 1)
      hD hepsilon (by norm_num)
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmallNat := hNatTop.eventually hsmall
  filter_upwards [eventually_clog_two_le_two_inv_log_mul_log,
    hsmallNat, eventually_ge_atTop 1] with A hclog hsmallA hA
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlogNonneg : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have hfront :
      (Nat.clog 2 A : ℝ) * (2 * C) ≤ D * Real.log A := by
    dsimp only [D]
    calc
      (Nat.clog 2 A : ℝ) * (2 * C) ≤
          (2 * (Real.log 2)⁻¹ * Real.log A) * (2 * C) :=
        mul_le_mul_of_nonneg_right hclog (mul_nonneg (by norm_num) hC)
      _ = 4 * C * (Real.log 2)⁻¹ * Real.log A := by ring
  have hfactor : D * Real.log A * (A : ℝ) ^ (-epsilon) ≤ 1 := by
    simpa only [Real.rpow_one] using hsmallA
  have hpowSplit :
      (A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon) =
        (A : ℝ) ^ (-epsilon) *
          (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
    rw [← Real.rpow_add hApos, ← Real.rpow_add hApos]
    congr 1
    ring
  calc
    (Nat.clog 2 A : ℝ) *
        (2 * C * (A : ℝ) ^ (4 * eta) *
          (A : ℝ) ^ (-3 * epsilon)) =
      ((Nat.clog 2 A : ℝ) * (2 * C)) *
        ((A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon)) := by ring
    _ ≤ (D * Real.log A) *
        ((A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon)) :=
      mul_le_mul_of_nonneg_right hfront (by positivity)
    _ = (D * Real.log A * (A : ℝ) ^ (-epsilon)) *
        (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
      rw [hpowSplit]
      ring
    _ ≤ 1 * (A : ℝ) ^ (4 * eta - 2 * epsilon) := by gcongr
    _ = _ := one_mul _

/-- One epsilon absorbs the terminal shell count and the exact
`ceil(log A)^(8 eta)` growth caused by inserting `n^(4 eta)`. -/
theorem eventually_pintz2023_middle_shell_endpoint_absorbed
    {C eta epsilon : ℝ} (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ A : ℕ in atTop,
      (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) *
          (C * (pintz2023GramCutoff A : ℝ) ^ (4 * eta) *
            (A : ℝ) ^ (-3 * epsilon)) ≤
        (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
  let D : ℝ := 8 * (Real.log 2)⁻¹ * C * 4 ^ (4 * eta)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hp : 0 < 8 * eta + 1 := by positivity
  have hsmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := D) (p := 8 * eta + 1) (q := epsilon) (b := 1)
      hD hepsilon (by norm_num)
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmallNat := hNatTop.eventually hsmall
  have hlogOne : ∀ᶠ A : ℕ in atTop, 1 ≤ Real.log A := by
    exact (Real.tendsto_log_atTop.comp hNatTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_clog_two_gramCutoff_le_eight_inv_log_mul_log,
    hsmallNat, hlogOne, eventually_ge_atTop 1] with
      A hclog hsmallA hlogA hA
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hlogNonneg : 0 ≤ Real.log A := zero_le_one.trans hlogA
  have hlogPos : 0 < Real.log A := zero_lt_one.trans_le hlogA
  have hM := pintz2023GramCutoff_cast_le_four_mul_log_sq hlogA
  have hMpow : (pintz2023GramCutoff A : ℝ) ^ (4 * eta) ≤
      4 ^ (4 * eta) * (A : ℝ) ^ (4 * eta) *
        (Real.log A) ^ (8 * eta) := by
    calc
      (pintz2023GramCutoff A : ℝ) ^ (4 * eta) ≤
          (4 * (A : ℝ) * (Real.log A) ^ 2) ^ (4 * eta) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hM (by positivity)
      _ = 4 ^ (4 * eta) * (A : ℝ) ^ (4 * eta) *
          ((Real.log A) ^ 2) ^ (4 * eta) := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * A)
          (sq_nonneg (Real.log A)),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg A)]
      _ = 4 ^ (4 * eta) * (A : ℝ) ^ (4 * eta) *
          (Real.log A) ^ (8 * eta) := by
        rw [← Real.rpow_natCast (Real.log A) 2,
          ← Real.rpow_mul hlogNonneg]
        congr 2
        norm_num
        ring
  have hfront :
      (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) * C *
          (pintz2023GramCutoff A : ℝ) ^ (4 * eta) ≤
        D * (Real.log A) ^ (8 * eta + 1) *
          (A : ℝ) ^ (4 * eta) := by
    calc
      (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) * C *
          (pintz2023GramCutoff A : ℝ) ^ (4 * eta) ≤
        (8 * (Real.log 2)⁻¹ * Real.log A) * C *
          (4 ^ (4 * eta) * (A : ℝ) ^ (4 * eta) *
            (Real.log A) ^ (8 * eta)) := by gcongr
      _ = D * (Real.log A) ^ (8 * eta + 1) *
          (A : ℝ) ^ (4 * eta) := by
        dsimp only [D]
        rw [Real.rpow_add hlogPos, Real.rpow_one]
        ring
  have hfactor :
      D * (Real.log A) ^ (8 * eta + 1) * (A : ℝ) ^ (-epsilon) ≤ 1 :=
    hsmallA
  have hpowSplit :
      (A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon) =
        (A : ℝ) ^ (-epsilon) *
          (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
    rw [← Real.rpow_add hApos, ← Real.rpow_add hApos]
    congr 1
    ring
  calc
    (Nat.clog 2 (pintz2023GramCutoff A) : ℝ) *
        (C * (pintz2023GramCutoff A : ℝ) ^ (4 * eta) *
          (A : ℝ) ^ (-3 * epsilon)) ≤
      (D * (Real.log A) ^ (8 * eta + 1) *
        (A : ℝ) ^ (4 * eta)) * (A : ℝ) ^ (-3 * epsilon) := by
      calc
        _ = ((Nat.clog 2 (pintz2023GramCutoff A) : ℝ) * C *
            (pintz2023GramCutoff A : ℝ) ^ (4 * eta)) *
              (A : ℝ) ^ (-3 * epsilon) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfront (by positivity)
    _ = (D * (Real.log A) ^ (8 * eta + 1) *
        (A : ℝ) ^ (-epsilon)) *
          (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
      calc
        D * (Real.log A) ^ (8 * eta + 1) *
            (A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon) =
          D * (Real.log A) ^ (8 * eta + 1) *
            ((A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon)) := by ring
        _ = D * (Real.log A) ^ (8 * eta + 1) *
            ((A : ℝ) ^ (-epsilon) *
              (A : ℝ) ^ (4 * eta - 2 * epsilon)) := by rw [hpowSplit]
        _ = _ := by ring
    _ ≤ 1 * (A : ℝ) ^ (4 * eta - 2 * epsilon) := by gcongr
    _ = _ := one_mul _

#print axioms eventually_clog_two_le_two_inv_log_mul_log
#print axioms eventually_clog_two_gramCutoff_le_eight_inv_log_mul_log
#print axioms eventually_pintz2023_low_shell_endpoint_absorbed
#print axioms eventually_pintz2023_middle_shell_endpoint_absorbed

end

end GafniTao
