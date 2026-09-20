import TaoTrudgianYang2025.ZetaSmoothDivisorTest

/-!
# The paid smooth-cutoff error

The constructed smooth source agrees with the retained finite source
on its inner band. Only actual off-band terms remain in the difference,
so the previous Gaussian damping pays for every transition term.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem norm_zetaSmoothDivisorSum_sub_short_le {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) :
    ‖zetaSmoothDivisorSum T G L - zetaShortQuadraticDivisorSum T G L‖ ≤
      (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) *
        (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) := by
  classical
  let S := zetaQuadraticDivisorBand T G L
  let f := fun n : ℕ => divisorWeight n * zetaSmoothDivisorTest T G L n
  let B := Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)
  have hf : Summable f := summable_zetaSmoothDivisorTerm hT hG hGT L
  have hc := summable_norm_zetaFrozenDivisorCoefficient hT
  have hpoint (n : {n : ℕ // n ∉ S}) : ‖f n‖ ≤ ‖zetaFrozenDivisorCoefficient T n‖ * B :=
    (norm_zetaSmoothDivisorTerm_le T G L n).trans
      (norm_zetaQuadraticDivisorTerm_off_band_le hT hG hGT hL.le n.2)
  have hfinite : zetaShortQuadraticDivisorSum T G L = ∑ n ∈ S, f n := by
    unfold zetaShortQuadraticDivisorSum
    exact Finset.sum_congr rfl (fun n hn => (zetaSmoothDivisorTerm_eq_on_band hT hG hL hn).symm)
  rw [hfinite]
  change ‖(∑' n, f n) - ∑ n ∈ S, f n‖ ≤ _
  rw [← hf.sum_add_tsum_subtype_compl S, add_sub_cancel_left]
  calc
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖f n‖ := norm_tsum_le_tsum_norm (hf.norm.subtype _)
    _ ≤ ∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖ * B :=
      (hf.norm.subtype _).tsum_le_tsum hpoint ((hc.subtype _).mul_right B)
    _ = (∑' n : {n : ℕ // n ∉ S}, ‖zetaFrozenDivisorCoefficient T n‖) * B := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Summable.tsum_subtype_le (fun n : ℕ => ‖zetaFrozenDivisorCoefficient T n‖)
        (fun n => n ∉ S) (fun _ => norm_nonneg _) hc) (by dsimp [B]; positivity)

theorem exists_norm_zetaSmoothDivisorSum_sub_short_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T → 0 < L →
      ‖zetaSmoothDivisorSum T G L - zetaShortQuadraticDivisorSum T G L‖ ≤
        C * T ^ (1 / 2 + ε) * G * Real.exp (-L ^ 2 / 8) := by
  obtain ⟨C, hC, hmass⟩ := exists_tsum_norm_source_divisor_weight_le ε hε
  refine ⟨C * Real.sqrt Real.pi, by positivity, ?_⟩
  intro T G L hT hG hGT hL
  apply (norm_zetaSmoothDivisorSum_sub_short_le (by linarith) hG hGT hL).trans
  have hm : (∑' n : ℕ, ‖zetaFrozenDivisorCoefficient T n‖) ≤ C * T ^ (1 / 2 + ε) := by
    simpa only [zetaFrozenDivisorCoefficient, norm_mul] using hmass T hT (-T)
  calc
    _ ≤ (C * T ^ (1 / 2 + ε)) * (Real.sqrt Real.pi * G * Real.exp (-L ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = _ := by ring

theorem exists_zetaSmoothDivisor_log_tail_bound (A : ℝ) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T G : ℝ, T₀ ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      ‖zetaSmoothDivisorSum T G (Real.log T) - zetaShortQuadraticDivisorSum T G (Real.log T)‖ ≤
        G * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaSmoothDivisorSum_sub_short_le (1 / 2) (by norm_num)
  obtain ⟨B, hB, htail⟩ := exists_logGaussian_power_tail_bound C 1 A (b := 1 / 8) (by norm_num)
  refine ⟨max 2 B, le_max_left _ _, ?_⟩
  intro T G hT hG hGT
  have hTB : B ≤ T := (le_max_right _ _).trans hT
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have h := hbound T G (Real.log T) (by linarith) hG hGT (Real.log_pos (by linarith))
  have he := mul_le_mul_of_nonneg_left (htail T hTB) hG.le
  rw [Real.rpow_one] at he
  norm_num only [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one] at h
  apply h.trans
  rw [show -(Real.log T) ^ 2 / 8 = -(1 / 8) * (Real.log T) ^ 2 by ring]
  calc
    _ = G * (C * T * Real.exp (-(1 / 8) * (Real.log T) ^ 2)) := by ring
    _ ≤ _ := he

end TaoTrudgianYang2025
