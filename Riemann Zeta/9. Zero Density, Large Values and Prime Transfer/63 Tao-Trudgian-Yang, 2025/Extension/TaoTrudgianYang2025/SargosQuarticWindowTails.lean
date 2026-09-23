import TaoTrudgianYang2025.SargosQuarticLocalNonstationary

/-! Both omitted tails of the actual centered quartic integral, uniformly in cutoff width. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem sargosQuarticCenteredIntegrand_integrable {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hs : HasCompactSupport χ) (ε r T : ℝ) :
    Integrable (fun u : ℝ => (χ u : ℂ)*(𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)) := by
  have hp : Continuous (fun u => T*sargosQuarticCenteredPhase ε r u) :=
    continuous_const.mul (sargosQuarticCenteredPhase_contDiff ε r).continuous
  have hc : Continuous (fun u : ℝ => (χ u : ℂ)*
      (𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)) :=
    (Complex.continuous_ofReal.comp hχ).mul
      ((continuous_subtype_val.comp Real.continuous_fourierChar).comp hp)
  exact hc.integrable_of_hasCompactSupport
    ((hs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right)

theorem sargosQuarticBufferedMode_sub_window {ε r T l b η H : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hT : 0 < T)
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hH : 0 < H)
    (hleft : -H ∈ sargosQuarticMorseRange ε r) (hright : H ∈ sargosQuarticMorseRange ε r)
    (hcutleft : l+η ≤ sargosQuarticMorseInverse ε r (-H))
    (hcutright : sargosQuarticMorseInverse ε r H ≤ b-η) :
    ‖sargosQuarticCenteredMode (modelPhaseBufferedCutoff l b η) ε r T-
      (∫ u in sargosQuarticMorseInverse ε r (-H)..sargosQuarticMorseInverse ε r H,
        (modelPhaseBufferedCutoff l b η u : ℂ)*(𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ))‖ ≤
      128/(7*Real.pi*T*H) := by
  let a := sargosQuarticMorseInverse ε r (-H)
  let c := sargosQuarticMorseInverse ε r H
  let lam := 7*T*H/16
  let g : ℝ → ℂ := fun u => (modelPhaseBufferedCutoff l b η u : ℂ)*
    (𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)
  have ha₀ := sargosQuarticMorseInverse_mem hε hr hleft
  have hc₀ := sargosQuarticMorseInverse_mem hε hr hright
  have hac : a ≤ c := by
    by_contra h
    have hm := sargosQuarticMorseCoordinate_strictMonoOn hε hr
      ⟨hc₀.1.le,hc₀.2.le⟩ ⟨ha₀.1.le,ha₀.2.le⟩ (lt_of_not_ge h)
    rw [sargosQuarticMorseCoordinate_inverse hleft,
      sargosQuarticMorseCoordinate_inverse hright] at hm
    linarith
  have ha : a ∈ Icc (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hc : c ∈ Icc (1 : ℝ) 2 := ⟨by linarith,by linarith⟩
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hgap := sargosQuarticMorseInverse_window_slope_gaps hε hr hH.le hleft hright
  have hmono : MonotoneOn (sargosQuarticSlope 1 ε) (Icc (1 : ℝ) 2) := by
    simpa only [mul_one] using (sargosQuarticSlope_strictMonoOn
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1)
      (by simpa using hε)).monotoneOn
  have hL : ‖∫ u in (l+η)..a, g u‖ ≤ 4/(lam*Real.pi) := by
    apply sargosQuarticBuffered_subinterval_nonstationary hε hT hη hcutleft
      (by linarith) ha.2 hlam
    right
    intro u hu
    have hu' : u ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hu.1],hu.2.trans ha.2⟩
    have hm := hmono hu' ha hu.2
    have hg := mul_le_mul_of_nonneg_left hgap.1 hT.le
    dsimp only [lam,a] at *
    nlinarith
  have hR : ‖∫ u in c..(b-η), g u‖ ≤ 4/(lam*Real.pi) := by
    apply sargosQuarticBuffered_subinterval_nonstationary hε hT hη hcutright
      hc.1 (by linarith) hlam
    left
    intro u hu
    have hu' : u ∈ Icc (1 : ℝ) 2 := ⟨hc.1.trans hu.1,by linarith [hu.2]⟩
    have hm := hmono hc hu' hu.1
    have hg := mul_le_mul_of_nonneg_left hgap.2 hT.le
    dsimp only [lam,c] at *
    nlinarith
  have hg : Integrable g := sargosQuarticCenteredIntegrand_integrable
    (modelPhaseBufferedCutoff_contDiff l b η).continuous
    (modelPhaseBufferedCutoff_hasCompactSupport hη) ε r T
  have hsupport : Function.support g ⊆ Ioc (l+η) (b-η) := by
    intro u hu
    have hχ : modelPhaseBufferedCutoff l b η u ≠ 0 := by
      intro hz
      exact hu (by simp only [g,hz,Complex.ofReal_zero,zero_mul])
    have hh := modelPhaseBufferedCutoff_support_open hη hχ
    exact ⟨hh.1,hh.2.le⟩
  have hsource : sargosQuarticCenteredMode (modelPhaseBufferedCutoff l b η) ε r T =
      ∫ u in (l+η)..(b-η), g u :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupport).symm
  have he₁ := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable : IntervalIntegrable g volume (l+η) a)
    (hg.intervalIntegrable : IntervalIntegrable g volume a c)
  have he₂ := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable : IntervalIntegrable g volume (l+η) c)
    (hg.intervalIntegrable : IntervalIntegrable g volume c (b-η))
  calc
    _ = ‖(∫ u in (l+η)..a, g u)+(∫ u in c..(b-η), g u)‖ := by
      rw [hsource,← he₂,← he₁]
      congr 1
      change ((∫ u in (l+η)..a, g u)+(∫ u in a..c, g u))+
        (∫ u in c..(b-η), g u)-(∫ u in a..c, g u) = _
      ring
    _ ≤ 4/(lam*Real.pi)+4/(lam*Real.pi) := (norm_add_le _ _).trans (add_le_add hL hR)
    _ = _ := by dsimp [lam]; ring

end TaoTrudgianYang2025

