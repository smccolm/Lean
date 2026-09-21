import TaoTrudgianYang2025.AtkinsonLeadingMajorant

/-!
# Quantitative coarse truncation of the actual leading series

The true divisor Dirichlet series at nine eighths controls the remaining
tail. The resulting polynomial cutoff is deliberately much longer than
the sharp Atkinson cutoff: stationary evaluation and localization remain open.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

def atkinsonLeadingFiniteSum (T G L : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, atkinsonLeadingTerm T G L n

theorem norm_divisorDirichletTerm_fiveQuarters_le_tail {N n : ℕ}
    (hN : 0 < N) (hNn : N ≤ n) :
    ‖divisorDirichletTerm (5 / 4) n‖ ≤ (N : ℝ) ^ (-(1 / 8 : ℝ)) *
      ‖divisorDirichletTerm (9 / 8) n‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hn0 : (0 : ℝ) < n := hN0.trans_le hNnR
  have hmono := Real.rpow_le_rpow_of_nonpos hN0 hNnR (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  have he : (n : ℝ) ^ (-(5 / 4 : ℝ)) =
      (n : ℝ) ^ (-(1 / 8 : ℝ)) * (n : ℝ) ^ (-(9 / 8 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have ha := norm_divisorDirichletTerm_real (5 / 4) n
  have hb := norm_divisorDirichletTerm_real (9 / 8) n
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at ha hb
  rw [ha, hb, he]
  have h := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hn0.le (-(9 / 8 : ℝ))))
    (norm_nonneg (divisorWeight n))
  nlinarith

theorem exists_norm_atkinsonLeadingSum_sub_finite_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ N : ℕ, 0 < N →
      ‖atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N‖ ≤
        C * G * T ^ (5 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingTerm_le
  let S : ℝ := ∑' n : ℕ, ‖divisorDirichletTerm (9 / 8) n‖
  have hS : 0 ≤ S := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C * (1 + S), by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth N hN
  have hT0 : 0 < T := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := summable_atkinsonLeadingTerm_of_secondOrder hT hG hGT hL hwidth
  have hsn := (summable_nat_add_iff N).2 hs
  have hd := (summable_divisorDirichletTerm (s := (9 / 8 : ℂ)) (by norm_num)).norm
  have hdn := (summable_nat_add_iff N).2 hd
  have he : atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N =
      ∑' n : ℕ, atkinsonLeadingTerm T G L (n + N) := by
    have h := hs.sum_add_tsum_nat_add N
    unfold atkinsonLeadingSum atkinsonLeadingFiniteSum
    linear_combination -h
  have htail : (∑' n : ℕ, ‖divisorDirichletTerm (9 / 8) (n + N)‖) ≤ S := by
    have h := hd.sum_add_tsum_nat_add N
    have hpos : 0 ≤ ∑ n ∈ Finset.range N, ‖divisorDirichletTerm (9 / 8) n‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [S]
    linarith
  let K : ℝ := C * G * T ^ (5 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  rw [he]
  calc
    _ ≤ ∑' n : ℕ, ‖atkinsonLeadingTerm T G L (n + N)‖ := norm_tsum_le_tsum_norm hsn.norm
    _ ≤ ∑' n : ℕ, K * ‖divisorDirichletTerm (9 / 8) (n + N)‖ := by
      apply hsn.norm.tsum_le_tsum _ (hdn.mul_left K)
      intro n
      apply (hbound T G L hT hG hGT hL hwidth (n + N)).trans
      have h := mul_le_mul_of_nonneg_left
        (norm_divisorDirichletTerm_fiveQuarters_le_tail hN (Nat.le_add_left N n))
        (show 0 ≤ C * G * T ^ (5 / 4 : ℝ) by positivity)
      simpa only [K, mul_assoc] using h
    _ = K * ∑' n : ℕ, ‖divisorDirichletTerm (9 / 8) (n + N)‖ := tsum_mul_left
    _ ≤ K * S := mul_le_mul_of_nonneg_left htail hK
    _ ≤ _ := by dsimp [K]; nlinarith

theorem exists_norm_atkinsonLeadingSum_sub_polynomial_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G → ∀ N : ℕ, T ^ (10 : ℝ) ≤ N →
      ‖atkinsonLeadingSum T G L - atkinsonLeadingFiniteSum T G L N‖ ≤ C * G := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_atkinsonLeadingSum_sub_finite_le
  refine ⟨C, hC, ?_⟩
  intro T G L hT hG hGT hL hwidth N hN
  have hT0 : 0 < T := by linarith
  have hp : 0 < T ^ (10 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hN0 : (0 : ℝ) < N := hp.trans_le hN
  have hmono := Real.rpow_le_rpow_of_nonpos hp hN (by norm_num : -(1 / 8 : ℝ) ≤ 0)
  have habsorb : T ^ (5 / 4 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hT0.le _)).trans
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
    norm_num
  apply (hbound T G L hT hG hGT hL hwidth N (by exact_mod_cast hN0)).trans
  have h := mul_le_mul_of_nonneg_left habsorb (show 0 ≤ C * G by positivity)
  simpa only [mul_assoc, mul_one] using h

end TaoTrudgianYang2025
