import TaoTrudgianYang2025.AtkinsonMainPartialSummation
import TaoTrudgianYang2025.AtkinsonMainWeightBounds
import TaoTrudgianYang2025.AtkinsonStationaryZetaSource

/-!
# Physical zeta consumers of the normalized main sums and Abel bound

The actual zeta integral is linked to the same ceiling cutoff, raw divisor
phases and separate signed weights. The width restriction is explicit.
The Abel quantity is not replaced by an unproved uniform variation bound.
-/

noncomputable section

open Complex MeasureTheory Filter

namespace TaoTrudgianYang2025

theorem exists_zetaSquarePhysicalGaussian_signedMain_approximation {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonCommonMainPhase T *
          (atkinsonPositiveMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
            atkinsonNegativeMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)))).re| ≤
          C*(G*Real.log T+T^(1/4+ε)) := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquarePhysicalGaussian_stationary_approximation hδ hε
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  have h := hsource T G hAT hlower hupper hquarter
  rwa [atkinsonStationaryLeadingSum_eq_signed hT0 hG hL hwidth] at h

theorem exists_zetaSquareLocalMean_le_mainAbel {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        4*Real.exp 1*atkinsonMainAbelBound T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))+
          C*(G*Real.log T+T^(1/4+ε)) := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquareLocalMean_le_stationary hδ hε
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  have h := hsource T G hAT hlower hupper hquarter
  have ha := (Complex.re_le_norm (atkinsonStationaryLeadingSum T G (Real.log T))).trans
    (norm_atkinsonStationaryLeadingSum_le_abel hT0 hG hL hwidth)
  have hm := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2*Real.exp 1)
  nlinarith

theorem exists_zetaSquarePhysicalGaussian_signedMain_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2) -
        2*(atkinsonCommonMainPhase T *
          (atkinsonPositiveMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
            atkinsonNegativeMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)))).re| ≤
          C*G*Real.log T := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquarePhysicalGaussian_stationary_above_fourthRoot hδ hκ
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  have h := hsource T G hAT hlower hupper hquarter
  rwa [atkinsonStationaryLeadingSum_eq_signed hT0 hG hL hwidth] at h

theorem exists_zetaSquareLocalMean_le_mainAbel_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        4*Real.exp 1*atkinsonMainAbelBound T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))+
          C*G*Real.log T := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquareLocalMean_le_stationary_above_fourthRoot hδ hκ
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  have h := hsource T G hAT hlower hupper hquarter
  have ha := (Complex.re_le_norm (atkinsonStationaryLeadingSum T G (Real.log T))).trans
    (norm_atkinsonStationaryLeadingSum_le_abel hT0 hG hL hwidth)
  have hm := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2*Real.exp 1)
  nlinarith

end TaoTrudgianYang2025

