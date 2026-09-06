import GafniTao.Pintz2023SmallBSourceBound
import GafniTao.ZeroSumSup

/-!
# Pintz (2023), the literal `A log^2 A` Gram cutoff

The paper truncates the smoothed zeta Gram series at `A_h log^2 A_h`.
We use the integer endpoint `A * ceil(log A)^2`.  The ceiling, the first
omitted integer, and the geometric denominator are retained in every bound.
-/

open Filter Topology

namespace GafniTao

noncomputable section

/-- Integer realization of Pintz's terminal Gram cutoff. -/
noncomputable def pintz2023GramCutoff (A : ℕ) : ℕ :=
  A * (Nat.ceil (Real.log A)) ^ 2

/-- Once `log A >= 1`, the integer cutoff contains the source endpoint `A`. -/
theorem le_pintz2023GramCutoff {A : ℕ}
    (hlog : 1 ≤ Real.log A) :
    A ≤ pintz2023GramCutoff A := by
  have hceil : 1 ≤ Nat.ceil (Real.log A) := by
    exact_mod_cast hlog.trans (Nat.le_ceil (Real.log A))
  unfold pintz2023GramCutoff
  exact Nat.le_mul_of_pos_right A (pow_pos hceil 2)

/-- The ceiling costs at most the explicit factor four in the logarithmic
square. -/
theorem pintz2023GramCutoff_cast_le_four_mul_log_sq {A : ℕ}
    (hlog : 1 ≤ Real.log A) :
    (pintz2023GramCutoff A : ℝ) ≤
      4 * (A : ℝ) * (Real.log A) ^ 2 := by
  have hlogNonneg : 0 ≤ Real.log A := zero_le_one.trans hlog
  have hceilLt : (Nat.ceil (Real.log A) : ℝ) < Real.log A + 1 :=
    Nat.ceil_lt_add_one hlogNonneg
  have hceil : (Nat.ceil (Real.log A) : ℝ) ≤ 2 * Real.log A := by
    linarith
  have hceilNonneg : (0 : ℝ) ≤ Nat.ceil (Real.log A) := by positivity
  unfold pintz2023GramCutoff
  push_cast
  calc
    (A : ℝ) * (Nat.ceil (Real.log A) : ℝ) ^ 2 ≤
        (A : ℝ) * (2 * Real.log A) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ = 4 * (A : ℝ) * (Real.log A) ^ 2 := by ring

/-- Pintz's small-`B_h` inequality leaves exactly one tenth of a power in
which to absorb `log^2 A`.  The integer ceiling only contributes the fixed
factor four. -/
theorem eventually_pintz2023GramCutoff_le_smallB_scale (r : ℕ)
    (hr : 0 < r) :
    ∀ᶠ A : ℕ in atTop, ∀ t : ℝ,
      1 ≤ t →
      (A : ℝ) ≤ t ^ (19 / (10 * (r : ℝ))) →
      (pintz2023GramCutoff A : ℝ) ≤ 4 * t ^ (2 / (r : ℝ)) := by
  have hlogPower := eventually_log_sq_le_rpow
    (show (0 : ℝ) < 1 / 19 by norm_num)
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogPowerNat := hNatTop.eventually hlogPower
  have hlogOne : ∀ᶠ A : ℕ in atTop, 1 ≤ Real.log A := by
    have hlogTop : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hNatTop
    exact hlogTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hlogPowerNat, hlogOne] with A hlogPowerA hlogA
  intro t ht hAt
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hApos : (0 : ℝ) < A := by
    by_contra hnot
    have hAzero : A = 0 := Nat.eq_zero_of_not_pos (by exact_mod_cast hnot)
    subst A
    norm_num at hlogA
  have hcut := pintz2023GramCutoff_cast_le_four_mul_log_sq hlogA
  have hAmono : (A : ℝ) ^ (1 / 19 : ℝ) ≤
      (t ^ (19 / (10 * (r : ℝ)))) ^ (1 / 19 : ℝ) := by
    exact Real.rpow_le_rpow hApos.le hAt (by norm_num)
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hpow :
      (t ^ (19 / (10 * (r : ℝ)))) ^ (1 / 19 : ℝ) =
        t ^ (1 / (10 * (r : ℝ))) := by
    rw [← Real.rpow_mul htpos.le]
    congr 1
    field_simp [hrReal.ne']
  have hAlog : (A : ℝ) * (Real.log A) ^ 2 ≤
      t ^ (2 / (r : ℝ)) := by
    calc
      (A : ℝ) * (Real.log A) ^ 2 ≤
          t ^ (19 / (10 * (r : ℝ))) * (A : ℝ) ^ (1 / 19 : ℝ) := by
        gcongr
      _ ≤ t ^ (19 / (10 * (r : ℝ))) *
          t ^ (1 / (10 * (r : ℝ))) := by
        gcongr
        simpa only [hpow] using hAmono
      _ = t ^ (2 / (r : ℝ)) := by
        rw [← Real.rpow_add htpos]
        congr 1
        field_simp [hrReal.ne']
        ring
  nlinarith

/-- Elementary lower bound for the geometric denominator in the complete
tail.  This is the quantitative form needed with kernel scale `A`. -/
theorem four_mul_inv_le_one_sub_exp_neg_half_inv {A : ℕ} (hA : 1 ≤ A) :
    (4 * (A : ℝ))⁻¹ ≤
      1 - Real.exp (-(1 : ℝ) / (2 * A)) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  let x : ℝ := 1 / (2 * A)
  have hxPos : 0 < x := by dsimp only [x]; positivity
  have hxHalf : x ≤ 1 / 2 := by
    dsimp only [x]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)]
    have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
    nlinarith
  have hxNorm : ‖-x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hxPos]
    linarith
  have hRem := Real.norm_exp_sub_one_sub_id_le hxNorm
  have hUpper : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
    have := (le_abs_self (Real.exp (-x) - 1 - (-x))).trans hRem
    simpa only [sub_neg_eq_add, Real.norm_eq_abs, abs_neg,
      abs_of_pos hxPos] using this
  have hMain : x / 2 ≤ 1 - Real.exp (-x) := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hEq : (4 * (A : ℝ))⁻¹ = x / 2 := by
    dsimp only [x]
    field_simp
    norm_num
  rw [hEq]
  simpa only [x, neg_div] using hMain

/-- The literal omitted tail after `A ceil(log A)^2` is smaller than every
fixed negative power, with an explicit factor four. -/
theorem eventually_pintz2023GramCutoff_tail_le (K : ℝ) :
    ∀ᶠ A : ℕ in atTop,
      Real.exp (-((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * A)))⁻¹ ≤
        4 * (A : ℝ) ^ (-K) := by
  have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hNatTop
  have hlogLarge := hlogTop.eventually
    (eventually_ge_atTop (max 1 (2 * (K + 1))))
  filter_upwards [hlogLarge, eventually_ge_atTop 1] with A hlog hA
  have hlogOne : 1 ≤ Real.log A := hlog.trans' (le_max_left _ _)
  have hlogK : 2 * (K + 1) ≤ Real.log A :=
    hlog.trans' (le_max_right _ _)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hAone : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hceil : Real.log A ≤ (Nat.ceil (Real.log A) : ℝ) :=
    Nat.le_ceil _
  have hceilNonneg : (0 : ℝ) ≤ Nat.ceil (Real.log A) := by positivity
  have hsq : (Real.log A) ^ 2 ≤ (Nat.ceil (Real.log A) : ℝ) ^ 2 := by
    nlinarith [Real.log_nonneg hAone]
  have hExponent : (K + 1) * Real.log A ≤
      ((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A) := by
    have hCutoff :
        (Nat.ceil (Real.log A) : ℝ) ^ 2 ≤
          ((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / A := by
      unfold pintz2023GramCutoff
      push_cast
      rw [le_div_iff₀ hApos]
      nlinarith
    have hlogSq : 2 * (K + 1) * Real.log A ≤
        (Real.log A) ^ 2 := by
      nlinarith [Real.log_nonneg hAone]
    have hHalf : (K + 1) * Real.log A ≤ (Real.log A) ^ 2 / 2 := by
      nlinarith
    have hCeilHalf : (Real.log A) ^ 2 / 2 ≤
        ((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A) := by
      have := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)
      have hCutoffHalf := div_le_div_of_nonneg_right hCutoff
        (by norm_num : (0 : ℝ) ≤ 2)
      calc
        (Real.log A) ^ 2 / 2 ≤
            (Nat.ceil (Real.log A) : ℝ) ^ 2 / 2 := this
        _ ≤ (((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / A) / 2 :=
          hCutoffHalf
        _ = ((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A) := by
          field_simp
    exact hHalf.trans hCeilHalf
  have hExp :
      Real.exp (-((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A)) ≤
        (A : ℝ) ^ (-(K + 1)) := by
    rw [Real.rpow_def_of_pos hApos]
    apply Real.exp_le_exp.mpr
    calc
      -((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A) ≤
          -(((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A)) := by
        ring_nf
        exact le_rfl
      _ ≤ -((K + 1) * Real.log A) := neg_le_neg hExponent
      _ = -(K + 1) * Real.log A := by ring
      _ = Real.log A * -(K + 1) := by ring
  have hdenPos : 0 < 1 - Real.exp (-(1 : ℝ) / (2 * A)) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hdenInv :
      (1 - Real.exp (-(1 : ℝ) / (2 * A)))⁻¹ ≤ 4 * A := by
    have hquarter := four_mul_inv_le_one_sub_exp_neg_half_inv hA
    have hinv := one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (4 * (A : ℝ))⁻¹) hquarter
    simpa only [one_div, inv_inv] using hinv
  calc
    Real.exp (-((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A)) *
        (1 - Real.exp (-(1 : ℝ) / (2 * A)))⁻¹
        ≤ (A : ℝ) ^ (-(K + 1)) * (4 * A) := by gcongr
    _ = 4 * (A : ℝ) ^ (-K) := by
      rw [show -(K + 1) = -K - 1 by ring, Real.rpow_sub_one hApos.ne']
      field_simp

#print axioms le_pintz2023GramCutoff
#print axioms pintz2023GramCutoff_cast_le_four_mul_log_sq
#print axioms eventually_pintz2023GramCutoff_le_smallB_scale
#print axioms four_mul_inv_le_one_sub_exp_neg_half_inv
#print axioms eventually_pintz2023GramCutoff_tail_le

end

end GafniTao
