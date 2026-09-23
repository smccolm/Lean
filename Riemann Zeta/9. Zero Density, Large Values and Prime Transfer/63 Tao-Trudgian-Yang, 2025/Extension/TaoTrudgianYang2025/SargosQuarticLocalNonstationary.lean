import TaoTrudgianYang2025.SargosQuarticWindowIntegral
import TaoTrudgianYang2025.BetaBufferedLocalNonstationary

/-! Width-independent original-cutoff integrals for the actual increasing quartic slope. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosQuarticBuffered_subinterval_nonstationary {ε r T l b η a c lam : ℝ}
    (hε : |ε| ≤ 1/96) (hT : 0 < T) (hη : 0 < η)
    (hac : a ≤ c) (ha : 1 ≤ a) (hc : c ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Icc a c, lam ≤ T*(sargosQuarticSlope 1 ε u-sargosQuarticSlope 1 ε r)) ∨
      (∀ u ∈ Icc a c, T*(sargosQuarticSlope 1 ε u-sargosQuarticSlope 1 ε r) ≤ -lam)) :
    ‖∫ u in a..c, (modelPhaseBufferedCutoff l b η u : ℂ)*
      (𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)‖ ≤ 4/(lam*Real.pi) := by
  let φ : ℝ → ℝ := fun u => -(T*sargosQuarticCenteredPhase ε r u)
  have hd (u : ℝ) : deriv φ u = -(T*(sargosQuarticSlope 1 ε u-sargosQuarticSlope 1 ε r)) :=
    (((sargosQuarticCenteredPhase_hasDerivAt ε r u).const_mul T).neg).deriv
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_const.mul (sargosQuarticCenteredPhase_contDiff ε r)).neg
  have hmono := (sargosQuarticSlope_strictMonoOn
    (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1)
    (by simpa using hε)).monotoneOn
  norm_num only [mul_one] at hmono
  have hs : Icc a c ⊆ Icc (1:ℝ) 2 := fun u hu => ⟨ha.trans hu.1,hu.2.trans hc⟩
  have hm : AntitoneOn (deriv φ) (Icc a c) := by
    intro u hu v hv huv
    rw [hd u,hd v]
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (sub_le_sub_right (hmono (hs hu) (hs hv) huv) _) hT.le)
  have hg : (∀ u ∈ Icc a c, lam ≤ deriv φ u) ∨ (∀ u ∈ Icc a c, deriv φ u ≤ -lam) := by
    rcases hgap with hp | hn
    · right
      intro u hu
      rw [hd]
      linarith [hp u hu]
    · left
      intro u hu
      rw [hd]
      linarith [hn u hu]
  have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := b) hη hac).fourierChar_of_closed_slope_gap
    hac hlam isOpen_univ (subset_univ _) (fun u _ =>
      hφ.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)) hm hg
  have he :
      (∫ u in a..c, (modelPhaseBufferedCutoff l b η u : ℂ)*
        (𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)) =
      conj (∫ u in a..c, (modelPhaseBufferedCutoff l b η u : ℂ)*(𝐞 (φ u) : ℂ)) := by
    simp only [intervalIntegral.integral_of_le hac]
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [φ]
    rw [map_mul (starRingEnd ℂ),Complex.conj_ofReal,sargos_fourier_conj]
  rw [he,Complex.norm_conj]
  convert h using 1
  norm_num

end TaoTrudgianYang2025
