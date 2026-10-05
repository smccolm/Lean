import DongWangWangZhang2026.DilationAssembly
import DongWangWangZhang2026.TwistBounds

/-!
# Uniform exponent absorption for the actual summatory dilation

The prime cutoff exponent and the parameter-integration loss are fixed
numerically, retaining a strict margin above the source exponent one third.
-/

namespace DongWangWangZhang2026
noncomputable section

/-- The optimized frequency scale retains the required exponent after both
the prime-cutoff and damping-parameter losses. -/
theorem optimized_dilation_scale_le_third {L b : ℝ} (hL : 1 ≤ L)
    (hb : 0 ≤ b) (hbL : b + 1 ≤ L) :
    (max b (L ^ (1 / 1000 : ℝ)) / L) ^ (3781 / 11300 : ℝ) ≤
      ((b + 1) / L) ^ (1 / 3 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hs0 : 0 < (b + 1) / L := by positivity
  have hs1 : (b + 1) / L ≤ 1 := (div_le_one hL0).mpr hbL
  rcases le_total b (L ^ (1 / 1000 : ℝ)) with hsmall | hlarge
  · rw [max_eq_right hsmall]
    have he : L ^ (1 / 1000 : ℝ) / L = L ^ (-999 / 1000 : ℝ) := by
      rw [show (-999 / 1000 : ℝ) = 1 / 1000 - 1 by norm_num, Real.rpow_sub hL0, Real.rpow_one]
    rw [he, ← Real.rpow_mul hL0.le]
    calc
      _ ≤ L ^ (-1 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = (1 / L) ^ (1 / 3 : ℝ) := by
        rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ b + 1) hL0.le) (by norm_num)
  · rw [max_eq_left hlarge]
    have hb0 : 0 < b := (Real.rpow_pos_of_pos hL0 _).trans_le hlarge
    have hr0 : 0 < b / L := div_pos hb0 hL0
    have hr1 : b / L ≤ 1 := (div_le_one hL0).mpr (by linarith)
    calc
      _ ≤ (b / L) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by norm_num)
      _ ≤ _ := Real.rpow_le_rpow hr0.le
        (div_le_div_of_nonneg_right (by linarith : b ≤ b + 1) hL0.le) (by norm_num)

theorem log_ratio_loss_le_third {s : ℝ} (hs : 0 < s) :
    s * Real.log (2 / s) ≤ 3 * s ^ (1 / 3 : ℝ) := by
  have hlog := mul_le_mul_of_nonneg_left
    (Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 2 / s)
      (by norm_num : (0 : ℝ) < 2 / 3)) hs.le
  have he : s * ((2 / s) ^ (2 / 3 : ℝ) / (2 / 3 : ℝ)) =
      (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * s ^ (1 / 3 : ℝ) := by
    have hp : s / s ^ (2 / 3 : ℝ) = s ^ (1 / 3 : ℝ) := by
      rw [show (1 / 3 : ℝ) = 1 - 2 / 3 by norm_num, Real.rpow_sub hs, Real.rpow_one]
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hs.le]
    calc
      _ = (3 / 2 : ℝ) * (2 : ℝ) ^ (2 / 3 : ℝ) * (s / s ^ (2 / 3 : ℝ)) := by ring
      _ = _ := by rw [hp]
  rw [he] at hlog
  have htwo := Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (2 / 3 : ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hs.le (1 / 3 : ℝ))
  linarith

theorem dilation_logarithmic_loss_le_third {L b Y : ℝ}
    (hL : 0 < L) (hb : 0 ≤ b) (hbL : b + 1 ≤ L) (hLY : L ≤ Y) (hYL : Y ≤ 2 * L) :
    (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1))) / Y ≤
      8 * ((b + 1) / L) ^ (1 / 3 : ℝ) := by
  let s := (b + 1) / L
  have ha : 0 < b + 1 := by linarith
  have hY : 0 < Y := hL.trans_le hLY
  have hs : 0 < s := div_pos ha hL
  have hs1 : s ≤ 1 := (div_le_one hL).mpr hbL
  have hlog0 : 0 ≤ Real.log (Y / (b + 1)) :=
    Real.log_nonneg ((one_le_div ha).mpr (hbL.trans hLY))
  have hlog : Real.log (Y / (b + 1)) ≤ Real.log (2 / s) := by
    apply Real.log_le_log (div_pos hY ha)
    dsimp only [s]
    have he : (2 : ℝ) / ((b + 1) / L) = (2 * L) / (b + 1) := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right hYL ha.le
  have hlogtop0 : 0 ≤ Real.log (2 / s) := hlog0.trans hlog
  have hnum : 0 ≤ 2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) := by positivity
  have hcoefficient : (2 + b) / L ≤ 2 * s := by dsimp only [s]; rw [← mul_div_assoc]; gcongr; linarith
  have hprod := mul_le_mul hcoefficient hlog hlog0 (by positivity : 0 ≤ 2 * s)
  have hsmall := Real.self_le_rpow_of_le_one hs.le hs1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hlarge := log_ratio_loss_le_third hs
  calc
    _ ≤ (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1))) / L :=
      div_le_div_of_nonneg_left hnum hL hLY
    _ = 2 * s + ((2 + b) / L) * Real.log (Y / (b + 1)) := by dsimp only [s]; ring
    _ ≤ 8 * s ^ (1 / 3 : ℝ) := by nlinarith only [hprod, hsmall, hlarge]

/-- An absolute coefficient for absorption of the optimized zeta product. -/
def dilationScaleConstant : ℝ := 8 * Real.exp (4 * (Real.log 4 + 4) + 12) + 20

theorem dilationScaleConstant_ge_one : 1 ≤ dilationScaleConstant := by
  unfold dilationScaleConstant
  have he := Real.exp_pos (4 * (Real.log 4 + 4) + 12)
  linarith

theorem dilation_maximum_le_scale {B L b : ℝ} (hL : 1 ≤ L)
    (hB : B ≤ L ^ (1 / 1000 : ℝ)) (hbL : b + 1 ≤ L) :
    4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
      (max B (max b (L ^ (1 / 1000 : ℝ))) / L) ^ (38 / 113 : ℝ) + 20 ≤
        dilationScaleConstant * L *
          (max b (L ^ (1 / 1000 : ℝ)) / L) ^ (38 / 113 : ℝ) := by
  have hL0 : 0 < L := by linarith
  let r := max b (L ^ (1 / 1000 : ℝ)) / L
  have hp1 : 1 ≤ L ^ (1 / 1000 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hpL : L ^ (1 / 1000 : ℝ) ≤ L := Real.rpow_le_self_of_one_le hL (by norm_num)
  have hr0 : 0 < r := div_pos (lt_of_lt_of_le (by positivity : (0 : ℝ) < L ^ (1 / 1000 : ℝ))
    (le_max_right _ _)) hL0
  have hr1 : r ≤ 1 := (div_le_one hL0).mpr (max_le (by linarith) hpL)
  have hrlow : 1 / L ≤ r := div_le_div_of_nonneg_right
    (hp1.trans (le_max_right _ _)) hL0.le
  have hpow := Real.self_le_rpow_of_le_one hr0.le hr1 (by norm_num : (38 / 113 : ℝ) ≤ 1)
  have hmass : 1 ≤ L * r ^ (38 / 113 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hrlow.trans hpow) hL0.le
    rw [mul_one_div_cancel hL0.ne'] at h
    exact h
  rw [max_eq_right (hB.trans (le_max_right _ _))]
  change 4 * Real.exp _ * (1 + L) * r ^ (38 / 113 : ℝ) + 20 ≤
    dilationScaleConstant * L * r ^ (38 / 113 : ℝ)
  have hfirst := mul_le_mul_of_nonneg_right (show 1 + L ≤ 2 * L by linarith)
    (show 0 ≤ 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * r ^ (38 / 113 : ℝ) by positivity)
  unfold dilationScaleConstant
  nlinarith only [hfirst, hmass]

/-- The evaluated spectral term is bounded at the exact target power. -/
theorem dilation_power_term_le_third {B L b : ℝ} (hL : 1 ≤ L)
    (hB : B ≤ L ^ (1 / 1000 : ℝ)) (hb : 0 ≤ b) (hbL : b + 1 ≤ L) :
    let U := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
      (max B (max b (L ^ (1 / 1000 : ℝ))) / L) ^ (38 / 113 : ℝ) + 20
    U ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 - (199 / 200 : ℝ)) *
      L ^ (1 - (199 / 200 : ℝ)) / (1 - (199 / 200 : ℝ)) ≤
        400 * dilationScaleConstant * L * ((b + 1) / L) ^ (1 / 3 : ℝ) := by
  let r := max b (L ^ (1 / 1000 : ℝ)) / L
  let U := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ (1 / 1000 : ℝ))) / L) ^ (38 / 113 : ℝ) + 20
  have hL0 : 0 < L := by linarith
  have hr : 0 ≤ r := div_nonneg (le_trans hb (le_max_left _ _)) hL0.le
  have hK := dilationScaleConstant_ge_one
  have hK0 : 0 ≤ dilationScaleConstant := zero_le_one.trans hK
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hmajor : U ≤ dilationScaleConstant * L * r ^ (38 / 113 : ℝ) :=
    dilation_maximum_le_scale hL hB hbL
  have hpower := Real.rpow_le_rpow hU hmajor (by norm_num : (0 : ℝ) ≤ 199 / 200)
  have hid : (dilationScaleConstant * L * r ^ (38 / 113 : ℝ)) ^ (199 / 200 : ℝ) *
      (2 : ℝ) ^ (1 - (199 / 200 : ℝ)) * L ^ (1 - (199 / 200 : ℝ)) /
        (1 - (199 / 200 : ℝ)) =
      200 * dilationScaleConstant ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 / 200 : ℝ) *
        L * r ^ (3781 / 11300 : ℝ) := by
    rw [Real.mul_rpow (mul_nonneg hK0 hL0.le) (Real.rpow_nonneg hr _),
      Real.mul_rpow hK0 hL0.le, ← Real.rpow_mul hr]
    norm_num only
    have hLL : L ^ (199 / 200 : ℝ) * L ^ (1 / 200 : ℝ) = L := by
      rw [← Real.rpow_add hL0]
      norm_num
    calc
      _ = 200 * dilationScaleConstant ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 / 200 : ℝ) *
          (L ^ (199 / 200 : ℝ) * L ^ (1 / 200 : ℝ)) * r ^ (3781 / 11300 : ℝ) := by ring
      _ = _ := by rw [hLL]
  have hfirst : U ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 - (199 / 200 : ℝ)) *
      L ^ (1 - (199 / 200 : ℝ)) / (1 - (199 / 200 : ℝ)) ≤
        200 * dilationScaleConstant ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 / 200 : ℝ) *
          L * r ^ (3781 / 11300 : ℝ) := by
    rw [← hid]
    gcongr
  have hconst := mul_le_mul
    (Real.rpow_le_self_of_one_le hK (by norm_num : (199 / 200 : ℝ) ≤ 1))
    (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 200 : ℝ) ≤ 1))
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hK0
  have hconst' : 200 * dilationScaleConstant ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 / 200 : ℝ) ≤
      400 * dilationScaleConstant := by nlinarith only [hconst]
  have hscale := optimized_dilation_scale_le_third hL hb hbL
  have hmiddle := mul_le_mul_of_nonneg_right hconst'
    (show 0 ≤ L * r ^ (3781 / 11300 : ℝ) by positivity)
  have hlast := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 400 * dilationScaleConstant * L by positivity)
  change U ^ (199 / 200 : ℝ) * _ * _ / _ ≤ _
  nlinarith only [hfirst, hmiddle, hlast]

/-- One absolute Lipschitz coefficient for all scalar losses. -/
def dilationLipschitzConstant : ℝ :=
  2048 * (8 + 1296 * meanValueAssemblyConstant * (400 * dilationScaleConstant + 2)) + 1904643

theorem dilationLipschitzConstant_ge_four : 4 ≤ dilationLipschitzConstant := by
  have hC := meanValueAssemblyConstant_pos
  have hK := dilationScaleConstant_ge_one
  have hp : 0 ≤ 1296 * meanValueAssemblyConstant * (400 * dilationScaleConstant + 2) := by positivity
  unfold dilationLipschitzConstant
  linarith only [hp]

/-- Complete scalar absorption of the evaluated actual-difference estimate. -/
theorem dilation_evaluated_bound_le_third {B L b Y : ℝ} (hL : 1 ≤ L)
    (hB : B ≤ L ^ (1 / 1000 : ℝ)) (hb : 0 ≤ b) (hbL : b + 1 ≤ L)
    (hLY : L ≤ Y) (hYL : Y ≤ 2 * L) :
    let U := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
      (max B (max b (L ^ (1 / 1000 : ℝ))) / L) ^ (38 / 113 : ℝ) + 20
    2048 / Y * (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
      1296 * meanValueAssemblyConstant *
        (U ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 - (199 / 200 : ℝ)) *
          L ^ (1 - (199 / 200 : ℝ)) / (1 - (199 / 200 : ℝ)) + 2)) +
        (1904642 + b) / Y ≤
      dilationLipschitzConstant * ((b + 1) / L) ^ (1 / 3 : ℝ) := by
  let U := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ (1 / 1000 : ℝ))) / L) ^ (38 / 113 : ℝ) + 20
  let P := U ^ (199 / 200 : ℝ) * (2 : ℝ) ^ (1 - (199 / 200 : ℝ)) *
    L ^ (1 - (199 / 200 : ℝ)) / (1 - (199 / 200 : ℝ))
  let s := ((b + 1) / L) ^ (1 / 3 : ℝ)
  have hL0 : 0 < L := by linarith
  have hY : 0 < Y := hL0.trans_le hLY
  have hC := meanValueAssemblyConstant_pos
  have hK := dilationScaleConstant_ge_one
  have hs : 0 ≤ s := by dsimp only [s]; positivity
  have hbase : (b + 1) / L ≤ s := Real.self_le_rpow_of_le_one (by positivity)
    ((div_le_one hL0).mpr hbL) (by norm_num)
  have hmass : b + 1 ≤ L * s := by
    have h := (div_le_iff₀ hL0).mp hbase
    nlinarith only [h]
  have hone : 1 ≤ L * s := by linarith
  have hP : 0 ≤ P := by dsimp only [P, U]; positivity
  have hpower : P ≤ 400 * dilationScaleConstant * L * s :=
    dilation_power_term_le_third hL hB hb hbL
  have hPbound : (P + 2) / Y ≤ (400 * dilationScaleConstant + 2) * s := by
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ P + 2) hL0 hLY).trans
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hpower, hone]
  have hlog := dilation_logarithmic_loss_le_third hL0 hb hbL hLY hYL
  have herr : (1904642 + b) / Y ≤ 1904643 * s := by
    apply (div_le_div_of_nonneg_left (by positivity : 0 ≤ 1904642 + b) hL0 hLY).trans
    apply (div_le_iff₀ hL0).mpr
    nlinarith only [hmass, hone]
  have hm := mul_le_mul_of_nonneg_left hPbound
    (show 0 ≤ 1296 * meanValueAssemblyConstant by positivity)
  change 2048 / Y * (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
    1296 * meanValueAssemblyConstant * (P + 2)) + (1904642 + b) / Y ≤
      dilationLipschitzConstant * s
  calc
    _ = 2048 * ((2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1))) / Y +
          1296 * meanValueAssemblyConstant * ((P + 2) / Y)) + (1904642 + b) / Y := by ring
    _ ≤ dilationLipschitzConstant * s := by
      unfold dilationLipschitzConstant
      nlinarith only [hlog, hm, herr]

/-- Uniform one-third control of the original difference at the same source
maximizer; all analytic and scale restrictions are discharged internally. -/
theorem exists_maximizingTwist_dilation_third_bound :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ b Y : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → b + 1 ≤ Real.log x →
      Real.log x ≤ Y → Y ≤ 2 * Real.log x →
      Real.exp (-Y) * ‖zetaSum (Real.exp Y) (t - t₀) -
        (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) (t - t₀)‖ ≤
          dilationLipschitzConstant * ((b + 1) / Real.log x) ^ (1 / 3 : ℝ) := by
  obtain ⟨B, hB, hsource⟩ := exists_maximizingTwist_dilation_power_bound 1000 (by norm_num)
    (q := (199 / 200 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨max 16 (B ^ (1000 : ℕ)), le_max_left _ _, ?_⟩
  intro x t t₀ b Y hx hlog hmax ht₀ hb hbL hLY hYL
  let L := Real.log x
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hlog
  have hL : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hpower : B ^ (1000 : ℝ) ≤ L := by
    rw [show (1000 : ℝ) = ((1000 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact (le_max_right (16 : ℝ) (B ^ (1000 : ℕ))).trans hlog
  have hBscale : B ≤ L ^ (1 / 1000 : ℝ) := by
    have h := (Real.le_rpow_inv_iff_of_pos hB0 hL0.le (by norm_num : (0 : ℝ) < 1000)).mpr hpower
    simpa only [one_div] using h
  have hBL : B ≤ L := hBscale.trans (Real.rpow_le_self_of_one_le hL (by norm_num))
  have h := hsource x t t₀ b Y hx hL16 hBL hmax ht₀ hb (hbL.trans hLY) hYL
  have he : (1000 : ℝ)⁻¹ = (1 / 1000 : ℝ) := by norm_num
  dsimp only at h
  simp only [Nat.cast_ofNat, he, add_assoc, show (16 : ℝ) + 4 = 20 by norm_num] at h
  have hs := dilation_evaluated_bound_le_third hL hBscale hb hbL hLY hYL
  dsimp only at hs
  simp only [add_assoc] at hs
  exact h.trans hs

theorem norm_normalized_dilation_eq (t b Y : ℝ) :
    ‖zetaSum (Real.exp Y) t / (Real.exp Y : ℂ) -
      zetaSum (Real.exp (Y - b)) t / (Real.exp (Y - b) : ℂ)‖ =
        Real.exp (-Y) * ‖zetaSum (Real.exp Y) t -
          (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) t‖ := by
  have hY : (Real.exp Y : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos Y).ne'
  have hb : (Real.exp b : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos b).ne'
  have he : zetaSum (Real.exp Y) t / (Real.exp Y : ℂ) -
      zetaSum (Real.exp (Y - b)) t / (Real.exp (Y - b) : ℂ) =
        (Real.exp (-Y) : ℂ) * (zetaSum (Real.exp Y) t -
          (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) t) := by
    rw [Real.exp_neg, Real.exp_sub]
    push_cast
    field_simp
  rw [he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The all-real logarithmic cutoff estimate at the original maximizing
twist, with one absolute threshold and the exact source exponent. -/
theorem exists_maximizingTwist_uniform_lipschitz :
    ∃ L₀ : ℝ, 16 ≤ L₀ ∧ ∀ x t t₀ : ℝ, 1 < x → L₀ ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → ∀ y : ℝ,
      ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
        zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)‖ ≤
          dilationLipschitzConstant *
            ((1 + |y - Real.log x|) / Real.log x) ^ (1 / 3 : ℝ) := by
  obtain ⟨L₀, hL₀, hsource⟩ := exists_maximizingTwist_dilation_third_bound
  refine ⟨L₀, hL₀, ?_⟩
  intro x t t₀ hx hlog hmax ht₀ y
  let L := Real.log x
  have hL16 : 16 ≤ L := hL₀.trans hlog
  have hL0 : 0 < L := by linarith
  change ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
    zetaSum (Real.exp L) (t - t₀) / (Real.exp L : ℂ)‖ ≤
      dilationLipschitzConstant * ((1 + |y - L|) / L) ^ (1 / 3 : ℝ)
  by_cases hnear : |y - L| ≤ L / 2
  · rcases le_total y L with hy | hy
    · have habs : |y - L| = L - y := by rw [abs_of_nonpos (sub_nonpos.mpr hy)]; ring
      have h := hsource x t t₀ (L - y) L hx hlog hmax ht₀
        (sub_nonneg.mpr hy) (by rw [habs] at hnear; linarith) le_rfl (by linarith)
      rw [← norm_normalized_dilation_eq, sub_sub_cancel] at h
      rw [norm_sub_rev] at h
      simpa only [habs, add_comm 1 (L - y)] using h
    · have habs : |y - L| = y - L := abs_of_nonneg (sub_nonneg.mpr hy)
      have h := hsource x t t₀ (y - L) y hx hlog hmax ht₀
        (sub_nonneg.mpr hy) (by rw [habs] at hnear; linarith) hy
        (by rw [habs] at hnear; linarith)
      rw [← norm_normalized_dilation_eq, sub_sub_cancel] at h
      simpa only [habs, add_comm 1 (y - L)] using h
  · have htrivial : ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
        zetaSum (Real.exp L) (t - t₀) / (Real.exp L : ℂ)‖ ≤ 2 := by
      have h := norm_sub_le (zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ))
        (zetaSum (Real.exp L) (t - t₀) / (Real.exp L : ℂ))
      linarith [norm_normalized_zetaSum_exp_le_one y (t - t₀),
        norm_normalized_zetaSum_exp_le_one L (t - t₀)]
    have hbase : (1 / 2 : ℝ) ≤ (1 + |y - L|) / L :=
      (le_div_iff₀ hL0).mpr (by linarith)
    have hp : (1 / 2 : ℝ) ≤ ((1 + |y - L|) / L) ^ (1 / 3 : ℝ) :=
      (Real.self_le_rpow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num) (by norm_num : (1 / 3 : ℝ) ≤ 1)).trans
          (Real.rpow_le_rpow (by norm_num) hbase (by norm_num))
    have hC := dilationLipschitzConstant_ge_four
    exact htrivial.trans (by nlinarith only [hp, hC])

/-- Full phase-specialized Lemma 2.2: one actual maximizing twist supplies
displacement, prime distance, all-real one-third continuity and reversed
comparison, with absolute constants and threshold. -/
theorem exists_large_sum_maximizing_twist :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          |t₀| ≤ C * N ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C ∧
          (∀ y : ℝ, ‖zetaSum (Real.exp y) (t - t₀) / (Real.exp y : ℂ) -
            zetaSum (Real.exp (Real.log x)) (t - t₀) / (Real.exp (Real.log x) : ℂ)‖ ≤
              C * ((1 + |y - Real.log x|) / Real.log x) ^ (1 / 3 : ℝ)) ∧
          ‖zetaSum x (t - t₀) -
            (((t₀ : ℂ) * Complex.I + 1) * (x : ℂ) ^ (-((t₀ : ℂ) * Complex.I))) *
              zetaSum x t‖ ≤ C * x / (Real.log x) ^ (3 / 4 : ℝ) := by
  obtain ⟨D, hD, x₁, hx₁, htwist⟩ := exists_large_sum_twist_bounds
  obtain ⟨L₀, hL₀, hlip⟩ := exists_maximizingTwist_uniform_lipschitz
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).eventually_ge_atTop 8)
  let C := D + dilationLipschitzConstant + 4
  have hClip := dilationLipschitzConstant_ge_four
  have hC : 0 < C := by dsimp only [C]; linarith
  have hCD : D ≤ C := by dsimp only [C]; linarith
  have hC4 : 4 ≤ C := by dsimp only [C]; linarith
  have hCL : dilationLipschitzConstant ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, max x₁ (Real.exp (max L₀ L₁)), hx₁.trans (le_max_left _ _), ?_⟩
  intro x hx₀ t N hN hNtop hsum
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hx₀
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlog : max L₀ L₁ ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (max L₀ L₁)) ((le_max_right _ _).trans hx₀)
    simpa only [Real.log_exp] using h
  have hlog₀ : L₀ ≤ Real.log x := (le_max_left _ _).trans hlog
  have hlog₁ : L₁ ≤ Real.log x := (le_max_right _ _).trans hlog
  have hL : 0 < Real.log x := Real.log_pos hx
  have hpower := hL₁ (Real.log x) hlog₁
  obtain ⟨t₀, ht₀, hmax, hdisplace, hM, hcomparison⟩ := htwist x hxx₁ t N hN hNtop hsum
  have hsmall : 8 * (Real.log x) ^ (1 / 100 : ℝ) ≤ Real.log x := by
    calc
      _ ≤ (Real.log x) ^ (99 / 100 : ℝ) * (Real.log x) ^ (1 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hL.le _)
      _ = _ := by rw [← Real.rpow_add hL]; norm_num
  have ht₀half : |t₀| ≤ Real.log x / 2 := by linarith
  refine ⟨t₀, ht₀, hmax, hdisplace.trans (mul_le_mul_of_nonneg_right hC4 (by linarith)),
    hM.trans (add_le_add le_rfl hCD), ?_, ?_⟩
  · intro y
    exact (hlip x t t₀ hx hlog₀ hmax ht₀half y).trans
      (mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg (by positivity) _))
  · exact hcomparison.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC4 hx0.le) (Real.rpow_nonneg hL.le _))

end
end DongWangWangZhang2026
