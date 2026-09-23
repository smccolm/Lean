import TaoTrudgianYang2025.SargosSixthStripCount
import TaoTrudgianYang2025.SargosLemmaOneMeasurable
import TaoTrudgianYang2025.SargosSlowLinear

/-! Source-height strips, including arbitrary slow phases, reduce to the actual base integral. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosSlowQuartic_upper_sixth_strip_reduction {N : ℕ} (hN : 2 ≤ N) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K lambda : ℝ} (hK : 0 ≤ K) (hlambda : 0 < lambda) (c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc c (c+1))).prod (volume.restrict (Icc d (d+lambda))))
      (fun t : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^6)) ≤
      ENNReal.ofReal (128*sargosWindowConstant 3 K*
        (1+lambda*(N : ℝ)^3)*(Real.log N)^6*sargosSixthBaseMoment N) := by
  have hu := sargosSlowQuartic_upper_even_window_le_count hN (by norm_num : 1 ≤ 3)
    z hz hK (by norm_num : (0 : ℝ) < 1) hlambda c d φ φ' hφ hφ'
  apply hu.trans
  apply ENNReal.ofReal_le_ofReal
  have hc := sargosMomentNearCount_unit_strip_le_base (by omega : 1 ≤ N) hlambda
  have hC := sargosWindowConstant_nonneg 3 hK
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  calc
    _ = (sargosWindowConstant 3 K*(Real.log N)^6)*
        (lambda*(sargosMomentNearCount N 3 (1/((1 : ℝ)*(N : ℝ)^2))
          (1/(lambda*(N : ℝ)^4)) : ℝ)) := by ring
    _ ≤ (sargosWindowConstant 3 K*(Real.log N)^6)*
        (128*(1+lambda*(N : ℝ)^3)*sargosSixthBaseMoment N) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

theorem sargosSlowQuartic_sixth_strip_reduction {N : ℕ} (hN : 2 ≤ N) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K lambda : ℝ} (hK : 0 ≤ K) (hlambda : 0 < lambda) (c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^6)
      ((volume.restrict (Icc c (c+1))).prod (volume.restrict (Icc d (d+lambda))))) :
    (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      (sargosSlowQuarticMaximum N z α γ (φ α γ))^6) ≤
      128*sargosWindowConstant 3 K*
        (1+lambda*(N : ℝ)^3)*(Real.log N)^6*sargosSixthBaseMoment N := by
  have hi := integrable_sargosSlowQuarticPower (by omega : 1 ≤ N) 6 z hK
    c (c+1) d (d+lambda) φ φ' hφ hφ' hm
  have hu := sargosSlowQuartic_upper_sixth_strip_reduction hN z hz hK hlambda c d φ φ' hφ hφ'
  rw [sargosUpperIntegral_ofReal_eq_integral hi
    (Eventually.of_forall (fun t => pow_nonneg
      (sargosSlowQuarticMaximum_nonneg N z t.1 t.2 (φ t.1 t.2)) 6)),
    integral_prod _ hi] at hu
  have hC := sargosWindowConstant_nonneg 3 hK
  have hI := sargosSixthBaseMoment_nonneg N
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu

theorem sargosQuartic_maximal_sixth_strip_reduction {N : ℕ} (hN : 2 ≤ N) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {lambda : ℝ} (hlambda : 0 < lambda) (c d : ℝ) :
    (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      (sargosQuarticPrefixMaximum N z α γ)^6) ≤
      128*sargosWindowConstant 3 0*
        (1+lambda*(N : ℝ)^3)*(Real.log N)^6*sargosSixthBaseMoment N := by
  have hφ : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N),
        HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Icc (N : ℝ) (2*N)) x := by
    intro α hα γ hγ x hx
    exact (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt
  have hφ' : ∀ α ∈ Icc c (c+1), ∀ γ ∈ Icc d (d+lambda),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖(0 : ℝ)‖ ≤ 0/(N : ℝ) := by
    intro α hα γ hγ x hx
    simp
  have hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (fun _ => 0))^6)
      ((volume.restrict (Icc c (c+1))).prod (volume.restrict (Icc d (d+lambda)))) := by
    simp_rw [sargosSlowQuarticMaximum_zero_phase]
    exact ((continuous_sargosQuarticPrefixMaximum N z).pow 6).aestronglyMeasurable
  have h := sargosSlowQuartic_sixth_strip_reduction hN z hz (le_refl (0 : ℝ)) hlambda
    c d (fun _ _ _ => 0) (fun _ _ _ => 0) hφ hφ' hm
  simpa only [sargosSlowQuarticMaximum_zero_phase] using h

end TaoTrudgianYang2025

