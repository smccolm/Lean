import TaoTrudgianYang2025.BetaBufferedLocalNonstationary

/-!
# Bounding both omitted tails of the original cutoff integral

The central endpoints are the actual inverse images of minus and plus H.
Their slope gaps and the width-independent cutoff variation bound the
difference between the whole original integral and its central piece.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem norm_bufferedNormalizedMode_sub_window_le
    {F : ℝ → ℝ} {σ δ T v l r η H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hH : 0 < H)
    (hleft : -H ∈ modelPhaseMorseRange F v) (hright : H ∈ modelPhaseMorseRange F v)
    (hcutleft : l+η ≤ modelPhaseMorseInverse F v (-H))
    (hcutright : modelPhaseMorseInverse F v H ≤ r-η) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v)-
      (∫ u in modelPhaseMorseInverse F v (-H)..modelPhaseMorseInverse F v H,
        (modelPhaseBufferedCutoff l r η u : ℂ)*(𝐞 (T*F u-(T*v)*u) : ℂ))‖ ≤
      8*Real.sqrt (σ+1)/(T*H*modelPhaseCurvatureLower σ*Real.pi) := by
  let a := modelPhaseMorseInverse F v (-H)
  let b := modelPhaseMorseInverse F v H
  let lam := T*(H*modelPhaseCurvatureLower σ/Real.sqrt (σ+1))
  let g : ℝ → ℂ := fun u => (modelPhaseBufferedCutoff l r η u : ℂ)*
    (𝐞 (T*F u-(T*v)*u) : ℂ)
  have ha : a ∈ Ioo (1 : ℝ) 2 := modelPhaseMorseInverse_mem hleft
  have hb : b ∈ Ioo (1 : ℝ) 2 := modelPhaseMorseInverse_mem hright
  have hlam : 0 < lam := by
    dsimp [lam]
    positivity [modelPhaseCurvatureLower_pos hσ]
  have hgap := modelPhaseMorseInverse_window_slope_gaps hσ hδ hF hv hH.le hleft hright
  have hmono := (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn
  have hL : ‖∫ u in (l+η)..a, g u‖ ≤ 4/(lam*Real.pi) := by
    apply norm_buffered_subinterval_nonstationary hσ hδ hF hT hη hcutleft
      (by linarith) ha.2 hlam
    left
    intro u hu
    have hu' : u ∈ Ioo (1 : ℝ) 2 := ⟨by linarith [hu.1],hu.2.trans_lt ha.2⟩
    have hm := hmono hu' ha hu.2
    have hg := mul_le_mul_of_nonneg_left hgap.1 hT.le
    dsimp only [lam,a] at *
    nlinarith
  have hR : ‖∫ u in b..(r-η), g u‖ ≤ 4/(lam*Real.pi) := by
    apply norm_buffered_subinterval_nonstationary hσ hδ hF hT hη hcutright
      hb.1 (by linarith) hlam
    right
    intro u hu
    have hu' : u ∈ Ioo (1 : ℝ) 2 := ⟨hb.1.trans_le hu.1,by linarith [hu.2]⟩
    have hm := hmono hb hu' hu.1
    have hg := mul_le_mul_of_nonneg_left hgap.2 hT.le
    dsimp only [lam,b] at *
    nlinarith
  have hg : Integrable g := modelPhaseNormalizedIntegrand_integrable
    (modelPhaseBufferedCutoff_contDiff l r η).continuous
    (modelPhaseBufferedCutoff_tsupport_model hη hl hr) hF T (T*v)
  have hsupport : Function.support g ⊆ Ioc (l+η) (r-η) := by
    intro u hu
    have hχ : modelPhaseBufferedCutoff l r η u ≠ 0 := by
      intro hz
      exact hu (by simp only [g,hz,Complex.ofReal_zero,zero_mul])
    have hh := modelPhaseBufferedCutoff_support_open hη hχ
    exact ⟨hh.1,hh.2.le⟩
  have hsource : modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T (T*v) =
      ∫ u in (l+η)..(r-η), g u :=
    (intervalIntegral.integral_eq_integral_of_support_subset hsupport).symm
  have he₁ := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable : IntervalIntegrable g volume (l+η) a)
    (hg.intervalIntegrable : IntervalIntegrable g volume a b)
  have he₂ := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable : IntervalIntegrable g volume (l+η) b)
    (hg.intervalIntegrable : IntervalIntegrable g volume b (r-η))
  calc
    _ = ‖(∫ u in (l+η)..a, g u)+(∫ u in b..(r-η), g u)‖ := by
      rw [hsource,← he₂,← he₁]
      congr 1
      change ((∫ u in (l+η)..a, g u)+(∫ u in a..b, g u))+
        (∫ u in b..(r-η), g u)-(∫ u in a..b, g u) = _
      ring
    _ ≤ 4/(lam*Real.pi)+4/(lam*Real.pi) := (norm_add_le _ _).trans (add_le_add hL hR)
    _ = _ := by
      dsimp [lam]
      field_simp
      ring

end TaoTrudgianYang2025
