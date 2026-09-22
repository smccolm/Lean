import TaoTrudgianYang2025.BetaBufferedNonstationary
import TaoTrudgianYang2025.BetaMorseWindowIntegral

/-!
# Original cutoff integrals away from the central Morse window

Slope gaps are needed only on the actual closed integration interval.
The cutoff has total variation at most two, independent of its width.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem IntervalC1Bound.fourierChar_of_closed_slope_gap
    {f : ℝ → ℂ} {φ : ℝ → ℝ} {a b M lam : ℝ} {J : Set ℝ}
    (hf : IntervalC1Bound f a b M) (hab : a ≤ b) (hlam : 0 < lam)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hφ : ∀ x ∈ J, ContDiffAt ℝ 2 φ x)
    (hmono : AntitoneOn (deriv φ) (Icc a b))
    (hgap : (∀ x ∈ Icc a b, lam ≤ deriv φ x) ∨
      (∀ x ∈ Icc a b, deriv φ x ≤ -lam)) :
    ‖∫ x in a..b, f x*(𝐞 (φ x) : ℂ)‖ ≤ 2*M/(lam*Real.pi) := by
  have h := hf.integral_mul_of_primitive_bound hab hJ hsub
    (k := fun x => (𝐞 (φ x) : ℂ))
    (by
      intro x hx
      have hc := (hφ x hx).continuousAt
      simp only [Real.fourierChar_apply]
      fun_prop)
    (B := 1/(lam*Real.pi)) (by
      intro x hx
      have hs : Icc a x ⊆ Icc a b := fun y hy => ⟨hy.1,hy.2.trans hx.2⟩
      apply norm_fourierCharIntegral_le_of_slope_gap hx.1 hlam
        (fun y hy => hφ y (hsub (hs hy)))
        (fun y hy z hz hyz => hmono (hs hy) (hs hz) hyz)
      rcases hgap with hp | hn
      · exact Or.inl (fun y hy => hp y (hs hy))
      · exact Or.inr (fun y hy => hn y (hs hy)))
  convert h using 1
  ring

theorem norm_buffered_subinterval_nonstationary
    {F : ℝ → ℝ} {σ δ T q l r η a b lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hab : a ≤ b)
    (ha : 1 < a) (hb : b < 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Icc a b, lam ≤ T*deriv F u-q) ∨
      (∀ u ∈ Icc a b, T*deriv F u-q ≤ -lam)) :
    ‖∫ u in a..b, (modelPhaseBufferedCutoff l r η u : ℂ)*
      (𝐞 (T*F u-q*u) : ℂ)‖ ≤ 4/(lam*Real.pi) := by
  let φ : ℝ → ℝ := fun u => T*F u-q*u
  have hs : Icc a b ⊆ Ioo (1 : ℝ) 2 :=
    fun u hu => ⟨ha.trans_le hu.1,hu.2.trans_lt hb⟩
  have hd {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
      deriv φ u = T*deriv F u-q := by
    have hFu := (approximateModelPhase_contDiffAt hF hu).differentiableAt (by simp)
    simpa only [φ,mul_one] using
      ((hFu.hasDerivAt.const_mul T).sub ((hasDerivAt_id u).const_mul q)).deriv
  have hφ : ∀ u ∈ Ioo (1 : ℝ) 2, ContDiffAt ℝ 2 φ u := by
    intro u hu
    exact (contDiffAt_const.mul ((approximateModelPhase_contDiffAt hF hu).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).sub
        (contDiffAt_const.mul contDiffAt_id)
  have hm : AntitoneOn (deriv φ) (Icc a b) := by
    intro u hu v hv huv
    rw [hd (hs hu),hd (hs hv)]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left
      ((approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn (hs hu) (hs hv) huv) hT.le) q
  have hg : (∀ u ∈ Icc a b, lam ≤ deriv φ u) ∨
      (∀ u ∈ Icc a b, deriv φ u ≤ -lam) := by
    rcases hgap with hp | hn
    · exact Or.inl (fun u hu => by rw [hd (hs hu)]; exact hp u hu)
    · exact Or.inr (fun u hu => by rw [hd (hs hu)]; exact hn u hu)
  have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := r) hη hab).fourierChar_of_closed_slope_gap
    hab hlam isOpen_Ioo hs hφ hm hg
  convert h using 1
  norm_num

theorem modelPhaseMorseInverse_window_slope_gaps
    {F : ℝ → ℝ} {σ δ v H : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hH : 0 ≤ H)
    (hleft : -H ∈ modelPhaseMorseRange F v) (hright : H ∈ modelPhaseMorseRange F v) :
    H*modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤
        deriv F (modelPhaseMorseInverse F v (-H))-v ∧
      H*modelPhaseCurvatureLower σ/Real.sqrt (σ+1) ≤
        v-deriv F (modelPhaseMorseInverse F v H) := by
  have hl := (modelPhaseMorseCoordinate_deriv_bounds hσ hδ hF hv
    (modelPhaseMorseInverse_mem hleft)).1
  have hr := (modelPhaseMorseCoordinate_deriv_bounds hσ hδ hF hv
    (modelPhaseMorseInverse_mem hright)).1
  have el := modelPhaseMorseCoordinate_deriv_mul hσ hδ hF hv (modelPhaseMorseInverse_mem hleft)
  have er := modelPhaseMorseCoordinate_deriv_mul hσ hδ hF hv (modelPhaseMorseInverse_mem hright)
  rw [modelPhaseMorseCoordinate_inverse hleft] at el
  rw [modelPhaseMorseCoordinate_inverse hright] at er
  have hl' := mul_le_mul_of_nonneg_left hl hH
  have hr' := mul_le_mul_of_nonneg_left hr hH
  rw [← mul_div_assoc] at hl' hr'
  constructor <;> nlinarith

end TaoTrudgianYang2025
