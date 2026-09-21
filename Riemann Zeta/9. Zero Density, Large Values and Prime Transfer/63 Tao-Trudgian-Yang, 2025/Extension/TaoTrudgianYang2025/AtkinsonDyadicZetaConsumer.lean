import TaoTrudgianYang2025.AtkinsonDyadicMain

/-!
# Actual Gaussian and local zeta means bounded by dyadic phase maxima

The complete stationary source is consumed, not assumed. Its proved
fourth-root-width error remains explicit. These bounds do not claim
a phase-sum Gram estimate or the critical twelfth moment.
-/

noncomputable section

open Complex MeasureTheory

namespace TaoTrudgianYang2025

theorem exists_zetaSquarePhysicalGaussian_le_dyadic {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T+T^(1/4+ε))) := by
  obtain ⟨C,hC,A,hA,hmain⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  obtain ⟨D,hD,B,_,hsource⟩ := exists_zetaSquarePhysicalGaussian_stationary_approximation hδ hε
  refine ⟨(2)*C+D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  have hT1 : 1 ≤ T := by linarith [hA.trans hAT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  let X := G*T^(-(1/4:ℝ))*
    atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))
  let Y := G*Real.log T+T^(1/4+ε)
  have hX : 0 ≤ X := mul_nonneg (by positivity) (atkinsonFullDyadicPhaseBound_nonneg _ _ _)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hm : (atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ C*X :=
    ((Complex.re_le_norm _).trans (hmain T G hAT hlower hupper)).trans_eq (by dsimp [X]; ring)
  have hs := hsource T G hBT hlower hupper hquarter
  have hscaled := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ 2)
  change (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤ ((2)*C+D)*(X+Y)
  have hsUpper := (abs_le.mp hs).2
  change (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2)-2*(atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ D*Y at hsUpper
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2)*C) hY,mul_nonneg hD.le hX]

theorem exists_zetaSquareLocalMean_le_dyadic {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T+T^(1/4+ε))) := by
  obtain ⟨C,hC,A,hA,hmain⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  obtain ⟨D,hD,B,_,hsource⟩ := exists_zetaSquareLocalMean_le_stationary hδ hε
  refine ⟨(2*Real.exp 1)*C+D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  have hT1 : 1 ≤ T := by linarith [hA.trans hAT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  let X := G*T^(-(1/4:ℝ))*
    atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))
  let Y := G*Real.log T+T^(1/4+ε)
  have hX : 0 ≤ X := mul_nonneg (by positivity) (atkinsonFullDyadicPhaseBound_nonneg _ _ _)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hm : (atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ C*X :=
    ((Complex.re_le_norm _).trans (hmain T G hAT hlower hupper)).trans_eq (by dsimp [X]; ring)
  have hs := hsource T G hBT hlower hupper hquarter
  have hscaled := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (2*Real.exp 1))
  change (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ ((2*Real.exp 1)*C+D)*(X+Y)
  change (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ (2*Real.exp 1)*(atkinsonStationaryLeadingSum T G (Real.log T)).re+D*Y at hs
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2*Real.exp 1)*C) hY,mul_nonneg hD.le hX]

theorem exists_zetaSquarePhysicalGaussian_le_dyadic_above_fourthRoot {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T)) := by
  obtain ⟨C,hC,A,hA,hmain⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  obtain ⟨D,hD,B,_,hsource⟩ := exists_zetaSquarePhysicalGaussian_stationary_above_fourthRoot hδ hκ
  refine ⟨(2)*C+D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  have hT1 : 1 ≤ T := by linarith [hA.trans hAT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  let X := G*T^(-(1/4:ℝ))*
    atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))
  let Y := G*Real.log T
  have hX : 0 ≤ X := mul_nonneg (by positivity) (atkinsonFullDyadicPhaseBound_nonneg _ _ _)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hm : (atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ C*X :=
    ((Complex.re_le_norm _).trans (hmain T G hAT hlower hupper)).trans_eq (by dsimp [X]; ring)
  have hs := hsource T G hBT hlower hupper hquarter
  rw [mul_assoc D G] at hs
  have hscaled := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ 2)
  change (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) ≤ ((2)*C+D)*(X+Y)
  have hsUpper := (abs_le.mp hs).2
  change (∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2)-2*(atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ D*Y at hsUpper
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2)*C) hY,mul_nonneg hD.le hX]

theorem exists_zetaSquareLocalMean_le_dyadic_above_fourthRoot {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        C*(G*T^(-(1/4:ℝ))*
          atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))+
            (G*Real.log T)) := by
  obtain ⟨C,hC,A,hA,hmain⟩ := exists_norm_atkinsonStationarySum_le_fullDyadic hδ
  obtain ⟨D,hD,B,_,hsource⟩ := exists_zetaSquareLocalMean_le_stationary_above_fourthRoot hδ hκ
  refine ⟨(2*Real.exp 1)*C+D,by positivity,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  have hT1 : 1 ≤ T := by linarith [hA.trans hAT]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
  let X := G*T^(-(1/4:ℝ))*
    atkinsonFullDyadicPhaseBound T G (atkinsonSourceCutoff T G (Real.log T))
  let Y := G*Real.log T
  have hX : 0 ≤ X := mul_nonneg (by positivity) (atkinsonFullDyadicPhaseBound_nonneg _ _ _)
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hm : (atkinsonStationaryLeadingSum T G (Real.log T)).re ≤ C*X :=
    ((Complex.re_le_norm _).trans (hmain T G hAT hlower hupper)).trans_eq (by dsimp [X]; ring)
  have hs := hsource T G hBT hlower hupper hquarter
  have hscaled := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (2*Real.exp 1))
  change (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ ((2*Real.exp 1)*C+D)*(X+Y)
  rw [mul_assoc D G] at hs
  change (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤ (2*Real.exp 1)*(atkinsonStationaryLeadingSum T G (Real.log T)).re+D*Y at hs
  nlinarith [mul_nonneg (by positivity : 0 ≤ (2*Real.exp 1)*C) hY,mul_nonneg hD.le hX]

end TaoTrudgianYang2025
