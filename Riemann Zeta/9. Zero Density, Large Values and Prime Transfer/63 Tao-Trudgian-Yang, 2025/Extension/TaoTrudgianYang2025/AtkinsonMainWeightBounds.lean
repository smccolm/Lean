import TaoTrudgianYang2025.AtkinsonSignedPhaseSeries

/-!
# Physical size and damping of the actual normalized main weights

The residual cutoff and Mellin profiles are bounded on their actual support.
The coefficient is linked to T and n and the Gaussian decay is retained.
This does not yet prove the discrete variation estimate required by Abel summation.
-/

noncomputable section

open Complex Set

namespace TaoTrudgianYang2025

theorem atkinsonCommonSaddleFactor_le_height {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonCommonSaddleFactor T b ≤
      ((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*T^(-(1/4:ℝ)) := by
  have hbase : 0 < (2/Real.pi)*T := by positivity
  have hl : (2/Real.pi)*T ≤ b^2+4*(T/(2*Real.pi)) := by
    rw [show 4*(T/(2*Real.pi)) = (2/Real.pi)*T by ring]
    nlinarith [sq_nonneg b]
  rw [atkinsonCommonSaddleFactor_eq_rpow hT]
  apply (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hbase hl (by norm_num : -(1/4:ℝ) ≤ 0))
      (by positivity : 0 ≤ 1/Real.sqrt 2)).trans_eq
  rw [Real.mul_rpow (by positivity) hT.le]
  ring

theorem atkinsonFourthRootCoefficient_nonneg {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 ≤ atkinsonFourthRootCoefficient T n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (atkinsonCommonSaddleFactor_pos hT _).le

theorem atkinsonFourthRootCoefficient_le_height {T : ℝ} (hT : 0 < T) (n : ℕ) :
    atkinsonFourthRootCoefficient T n ≤
      ((1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ)))*
        T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ)) := by
  apply (mul_le_mul_of_nonneg_left (atkinsonCommonSaddleFactor_le_height hT (Real.sqrt n))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans_eq
  ring

theorem exists_norm_atkinsonSaddleResidual_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ, 0 < T → 0 < G → 0 < L →
      8*L ≤ G → ‖atkinsonSaddleResidual T G L b‖ ≤ C := by
  obtain ⟨C,hC,hprofile⟩ := exists_intervalC1Bound_zetaMainMellinProfile
  refine ⟨C,hC,?_⟩
  intro T G L b hT hG hL hwidth
  by_cases hc : zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) = 0
  · simp only [atkinsonSaddleResidual,hc,Complex.ofReal_zero,mul_zero,norm_zero]
    exact hC.le
  · have hs := support_zetaDivisorBandCutoff hT hG hL hc
    have hb := zetaDivisorBandEdge_outer_bounds hT hG hL.le hwidth
    have hlo : T/16 ≤ T/(4*Real.pi) := div_le_div_of_nonneg_left hT.le
      (by positivity) (by nlinarith [Real.pi_lt_four])
    have hhi : T/Real.pi ≤ T := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [Real.pi_gt_three]
    have hx : zetaAtkinsonSaddle T b ∈ Icc (T/16) T :=
      ⟨hlo.trans (hb.1.trans hs.1),(hs.2.trans hb.2).trans hhi⟩
    have hp := (hprofile T hT).norm_le _ hx
    have hcut : ‖(zetaDivisorBandCutoff T G L (zetaAtkinsonSaddle T b) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real,Real.norm_eq_abs]
      change |zetaBandCutoff _ _ _ _ _| ≤ 1
      rw [abs_of_nonneg (zetaBandCutoff_nonneg _ _ _ _ _)]
      exact zetaBandCutoff_le_one _ _ _ _ _
    unfold atkinsonSaddleResidual
    rw [norm_mul]
    exact (mul_le_mul hp hcut (norm_nonneg _) hC.le).trans_eq (mul_one C)

theorem exists_norm_atkinsonMainWeights_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 0 < T → 0 < G → G^2 ≤ 2*T →
      0 < L → 8*L ≤ G → ∀ n : ℕ, (n:ℝ) ≤ T →
      ‖atkinsonPositiveMainWeight T G L n‖ ≤
        C*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*
          Real.exp (-(G^2*(n:ℝ))/(12*T)) ∧
      ‖atkinsonNegativeMainWeight T G L n‖ ≤
        C*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*
          Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
  obtain ⟨D,hD,hres⟩ := exists_norm_atkinsonSaddleResidual_le
  let K : ℝ := (1/Real.sqrt 2)*(2/Real.pi)^(-(1/4:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K*Real.sqrt Real.pi*D,by positivity,?_⟩
  intro T G L hT hG hGT hL hwidth n hn
  have hc := atkinsonFourthRootCoefficient_le_height hT n
  have hg := norm_atkinsonSaddleGaussian_le_physical hT hG hGT n hn
  have hnorm : ‖(atkinsonFourthRootCoefficient T n : ℂ)‖ =
      atkinsonFourthRootCoefficient T n := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (atkinsonFourthRootCoefficient_nonneg hT n)]
  have hbound (b : ℝ) :
      ‖(atkinsonFourthRootCoefficient T n : ℂ)*atkinsonSaddleGaussian T G n*
        atkinsonSaddleResidual T G L b‖ ≤
        (K*Real.sqrt Real.pi*D)*G*T^(-(1/4:ℝ))*(n:ℝ)^(-(1/4:ℝ))*
          Real.exp (-(G^2*(n:ℝ))/(12*T)) := by
    rw [norm_mul,norm_mul,hnorm]
    apply (mul_le_mul
      (mul_le_mul hc hg (norm_nonneg _) (by positivity))
      (hres T G L b hT hG hL hwidth) (norm_nonneg _) (by positivity)).trans_eq
    dsimp [K]
    ring
  exact ⟨hbound (Real.sqrt n),hbound (-Real.sqrt n)⟩

end TaoTrudgianYang2025
