import TaoTrudgianYang2025.AtkinsonStationarySumError

/-!
# Actual physical zeta consumers of the summed stationary estimate

The complete evaluated series, both signs and all original coefficients
are retained. The error is C(G log(T) + T^(1/4+epsilon)); above
T^(1/4+kappa) it is C G log(T). These are not claims about the
unproved smaller-width sharp Atkinson range or final moment assembly.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

private theorem one_le_log_of_stationary_height {T : ℝ} (hT : 40000 ≤ T) :
    1 ≤ Real.log T := by
  apply (Real.le_log_iff_exp_le (by linarith : 0 < T)).2
  have h := exp_sub_one_le_two_mul (by norm_num : (0:ℝ) ≤ 1) le_rfl
  linarith

theorem exists_zetaSquarePhysicalGaussian_stationary_approximation {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonStationaryLeadingSum T G (Real.log T)).re| ≤
          C*(G*Real.log T+T^(1/4+ε)) := by
  obtain ⟨C,hC,B,_,hsource⟩ := exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation hδ
  obtain ⟨D,hD,E,hE,herror⟩ := exists_atkinsonLeadingSum_sub_stationary_bound hδ hε
  refine ⟨C+2*D,by positivity,max B E,hE.trans (le_max_right _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hTlarge : 40000 ≤ T := hE.trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog := one_le_log_of_stationary_height hTlarge
  have hGlog : G ≤ G*Real.log T := le_mul_of_one_le_right hG.le hlog
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper hquarter
  have hr := (Complex.abs_re_le_norm (atkinsonLeadingSum T G (Real.log T) -
    atkinsonStationaryLeadingSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1,(abs_le.mp hm).2,
    (abs_le.mp hr).1,(abs_le.mp hr).2,Real.rpow_pos_of_pos hT0 (1/4+ε)]

theorem exists_zetaSquareLocalMean_le_stationary {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C*(G*Real.log T+T^(1/4+ε)) := by
  obtain ⟨C,hC,B,_,hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_leading hδ
  obtain ⟨D,hD,E,hE,herror⟩ := exists_atkinsonLeadingSum_sub_stationary_bound hδ hε
  refine ⟨C+2*Real.exp 1*D,by positivity,max B E,hE.trans (le_max_right _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hTlarge : 40000 ≤ T := hE.trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog := one_le_log_of_stationary_height hTlarge
  have hGlog : G ≤ G*Real.log T := le_mul_of_one_le_right hG.le hlog
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper hquarter
  have hr := (Complex.re_le_norm (atkinsonLeadingSum T G (Real.log T) -
    atkinsonStationaryLeadingSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*Real.exp 1)
  have hGscaled := mul_le_mul_of_nonneg_left hGlog (by positivity : 0 ≤ 2*Real.exp 1*D)
  nlinarith [Real.rpow_pos_of_pos hT0 (1/4+ε)]

theorem exists_zetaSquarePhysicalGaussian_stationary_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonStationaryLeadingSum T G (Real.log T)).re| ≤ C*G*Real.log T := by
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_zetaSquarePhysicalGaussian_stationary_approximation hδ hκ
  refine ⟨2*C,by positivity,B,hB,?_⟩
  intro T G hT hlower hupper hquarter
  have hTlarge : 40000 ≤ T := hB.trans hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hq : T^(1/4 : ℝ) ≤ G :=
    (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1/4:ℝ) ≤ 1/4+κ)).trans hquarter
  have hGlog : G ≤ G*Real.log T :=
    le_mul_of_one_le_right hG.le (one_le_log_of_stationary_height hTlarge)
  apply (hbound T G hT hlower hupper hq).trans
  nlinarith

theorem exists_zetaSquareLocalMean_le_stationary_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum T G (Real.log T)).re +
          C*G*Real.log T := by
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_zetaSquareLocalMean_le_stationary hδ hκ
  refine ⟨2*C,by positivity,B,hB,?_⟩
  intro T G hT hlower hupper hquarter
  have hTlarge : 40000 ≤ T := hB.trans hT
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hq : T^(1/4 : ℝ) ≤ G :=
    (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1/4:ℝ) ≤ 1/4+κ)).trans hquarter
  have hGlog : G ≤ G*Real.log T :=
    le_mul_of_one_le_right hG.le (one_le_log_of_stationary_height hTlarge)
  have h := hbound T G hT hlower hupper hq
  nlinarith

end TaoTrudgianYang2025
