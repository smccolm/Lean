import Dubon2026.GammaRieszKernelDerivative
import Dubon2026.SecondDifferenceDerivative

/-! # Low-frequency second differences of the genuine weighted Riesz Gamma kernel -/

namespace Dubon2026

open Complex Set

noncomputable section

/-- The actual second forward difference of the weighted order-two kernel. -/
def gammaRieszSecondDifference (k c x h : ℝ) : ℂ :=
  ((x + 2 * h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + 2 * h)) -
    2 * (((x + h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + h))) +
      (x : ℂ) ^ 2 * gammaRieszKernel k 2 (c * x)

/-- The genuine kernel derivatives and sharp order-zero bound give the low-frequency second-difference estimate. -/
theorem exists_gammaRieszSecondDifference_low_bound {k : ℝ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ c x h : ℝ, 0 < c → 0 < x → 0 ≤ h → h ≤ x →
      ‖gammaRieszSecondDifference k c x h‖ ≤ C * h ^ 2 * (c * x) ^ (3 / 8 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_gammaRieszKernel_bound hk (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2)
  simp only [zero_div, sub_zero] at hbound
  refine ⟨C * (3 : ℝ) ^ (3 / 8 : ℝ), by positivity, ?_⟩
  intro c x h hc hx hh hhx
  have hb (y : ℝ) (hy : y ∈ Icc x (x + 2 * h)) :
      ‖gammaRieszKernel k 0 (c * y)‖ ≤ C * (3 : ℝ) ^ (3 / 8 : ℝ) * (c * x) ^ (3 / 8 : ℝ) := by
    have hy0 : 0 < y := hx.trans_le hy.1
    calc
      _ ≤ C * (c * y) ^ (3 / 8 : ℝ) := hbound (c * y) (mul_pos hc hy0)
      _ ≤ C * (3 * (c * x)) ^ (3 / 8 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.rpow_le_rpow (mul_pos hc hy0).le _ (by norm_num)
        nlinarith [hy.2]
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (mul_pos hc hx).le]; ring
  have hm := norm_secondDifference_le_of_hasDerivAt hh
    (fun y hy => hasDerivAt_gammaRieszKernel_two hk hc (hx.trans_le hy.1))
    (fun y hy => hasDerivAt_gammaRieszKernel_one hk hc (hx.trans_le hy.1)) hb
  exact hm.trans_eq (by ring)

/-- The actual order-two power bound controls the high-frequency second difference without differentiating it. -/
theorem exists_gammaRieszSecondDifference_high_bound {k : ℝ} (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ c x h : ℝ, 0 < c → 0 < x → 0 ≤ h → h ≤ x →
      ‖gammaRieszSecondDifference k c x h‖ ≤ C * c ^ (-(1 / 8 : ℝ)) * x ^ (15 / 8 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_gammaRieszKernel_bound hk (by norm_num : (0 : ℝ) ≤ 2) (le_refl (2 : ℝ))
  norm_num only [show (3 / 8 : ℝ) - 2 / 4 = -(1 / 8 : ℝ) by norm_num] at hbound
  refine ⟨36 * C, by positivity, ?_⟩
  intro c x h hc hx hh hhx
  have hb (y : ℝ) (hy : y ∈ Icc x (3 * x)) :
      ‖(y : ℂ) ^ 2 * gammaRieszKernel k 2 (c * y)‖ ≤
        9 * C * c ^ (-(1 / 8 : ℝ)) * x ^ (15 / 8 : ℝ) := by
    have hy0 : 0 < y := hx.trans_le hy.1
    have hn := Real.rpow_le_rpow_of_nonpos (mul_pos hc hx)
      (mul_le_mul_of_nonneg_left hy.1 hc.le) (by norm_num : -(1 / 8 : ℝ) ≤ 0)
    have hp : x ^ 2 * x ^ (-(1 / 8 : ℝ)) = x ^ (15 / 8 : ℝ) := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
      norm_num
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    calc
      _ ≤ (9 * x ^ 2) * (C * (c * x) ^ (-(1 / 8 : ℝ))) := by
        apply mul_le_mul
        · nlinarith [sq_nonneg (3 * x - y), mul_nonneg (sub_nonneg.mpr hy.2) (show 0 ≤ 3 * x + y by linarith)]
        · exact (hbound (c * y) (mul_pos hc hy0)).trans (mul_le_mul_of_nonneg_left hn hC.le)
        · exact norm_nonneg _
        · positivity
      _ = _ := by
        rw [Real.mul_rpow hc.le hx.le]
        calc
          _ = 9 * C * c ^ (-(1 / 8 : ℝ)) * (x ^ 2 * x ^ (-(1 / 8 : ℝ))) := by ring
          _ = _ := by rw [hp]
  have h0 := hb x ⟨le_rfl, by linarith⟩
  have h1 := hb (x + h) ⟨by linarith, by linarith⟩
  have h2 := hb (x + 2 * h) ⟨by linarith, by linarith⟩
  unfold gammaRieszSecondDifference
  calc
    _ ≤ ‖((x + 2 * h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + 2 * h))‖ +
        ‖2 * (((x + h : ℝ) : ℂ) ^ 2 * gammaRieszKernel k 2 (c * (x + h)))‖ +
          ‖(x : ℂ) ^ 2 * gammaRieszKernel k 2 (c * x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by
      rw [norm_mul (2 : ℂ), Complex.norm_ofNat]
      nlinarith

end
end Dubon2026
