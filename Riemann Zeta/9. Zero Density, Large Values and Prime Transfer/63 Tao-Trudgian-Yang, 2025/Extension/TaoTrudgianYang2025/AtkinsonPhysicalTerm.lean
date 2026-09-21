import TaoTrudgianYang2025.AtkinsonCutoffPowers

/-!
# Physical two-term estimate before logarithmic absorption

The diagonal and near terms have scale R H/G; the far term has
scale R² sqrt(G L). This lemma estimates the literal closed budget.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem atkinsonPowerGapTerm_epsilon_factor {N : ℕ} (hN : 0 < N)
    (η H G L : ℝ) (R : ℕ) :
    atkinsonPowerGapTerm η H G L N R =
      (N:ℝ)^η*atkinsonPowerGapTerm 0 H G L N R := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  unfold atkinsonPowerGapTerm
  simp only [add_zero,Real.rpow_add hN0]
  ring

theorem atkinsonPhysical_gap_term_zero_le {H G : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hlog : 1 ≤ Real.log (2*H))
    (hN : (N:ℝ) ≤ H) (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm 0 H G L N R ≤
      148000*(Real.log (2*H))^3*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hlog0 : 0 < Real.log (2*H) := by linarith
  let P := G^2*H^(-(1/2:ℝ))
  let B := 74*H*(Real.log (2*H))^2/G^2
  let K := (harmonic (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)):ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by
    simpa only [harmonic_zero,Rat.cast_zero] using atkinson_harmonic_mono
      (Nat.zero_le (Nat.ceil (Real.sqrt (H*(N:ℝ))/G)))
  have hk : K ≤ 2*Real.log (2*H) := atkinson_harmonic_le_height_log hH hG hlog hN
  have hdiag : P*(N:ℝ)^(3/2:ℝ) ≤ 5476*(H/G)*(Real.log (2*H))^3 := by
    calc
      _ ≤ P*B^(3/2:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ ≤ _ := atkinsonPhysical_diagonal_scale hH0 hG0 hlog0
  have hnear : (Real.sqrt H/G)*(P*(N:ℝ)^(1:ℝ)) ≤
      74*(H/G)*(Real.log (2*H))^2 := by
    calc
      _ ≤ (Real.sqrt H/G)*(P*B^(1:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ = _ := atkinsonPhysical_near_scale hH0 hG0 hlog0
  have hfar : (H^(-(1/4:ℝ))*Real.sqrt L)*(P*(N:ℝ)^(3/4:ℝ)) ≤
      74*Real.sqrt (G*L)*(Real.log (2*H))^3 := by
    calc
      _ ≤ (H^(-(1/4:ℝ))*Real.sqrt L)*(P*B^(3/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg N) hcut (by norm_num)) hP
      _ ≤ _ := atkinsonPhysical_far_scale hH0 hG0 hlog
  have hd := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg R : (0:ℝ) ≤ _)
  have hn := mul_le_mul
    (mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ 120*(R:ℝ)))
    hk hK (by positivity)
  have hf := mul_le_mul_of_nonneg_left hfar (by positivity : 0 ≤ 2000*(R:ℝ)^2)
  have hsum := add_le_add (add_le_add hd hn) hf
  have he : P*atkinsonPowerGapTerm 0 H G L N R =
      (R:ℝ)*(P*(N:ℝ)^(3/2:ℝ))+
      (120*(R:ℝ)*((Real.sqrt H/G)*(P*(N:ℝ)^(1:ℝ))))*K+
      2000*(R:ℝ)^2*((H^(-(1/4:ℝ))*Real.sqrt L)*(P*(N:ℝ)^(3/4:ℝ))) := by
    unfold atkinsonPowerGapTerm K
    simp only [add_zero]
    ring
  change P*atkinsonPowerGapTerm 0 H G L N R ≤ _
  rw [he]
  apply hsum.trans
  have hpos : 0 ≤ (R:ℝ)*(H/G)*(Real.log (2*H))^3 := by positivity
  ring_nf at hpos ⊢
  nlinarith

end TaoTrudgianYang2025
