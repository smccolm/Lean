import TaoTrudgianYang2025.SargosQuarticFourierCurvature

/-! Actual support-exterior Fourier modes from the quartic endpoint slopes.
No model phase or supplied nonstationary estimate is used. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosQuarticBufferedFourierMode_of_slope_gap {N α γ y l b η lam : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Icc (l+η) (b-η), lam ≤ sargosQuarticSlope α γ (N*u)-y) ∨
      (∀ u ∈ Icc (l+η) (b-η), sargosQuarticSlope α γ (N*u)-y ≤ -lam)) :
    ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤ 4/(lam*Real.pi) := by
  rw [sargosQuarticFourierMode_eq_normalized _ hN,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  by_cases hab : l+η ≤ b-η
  · let φ : ℝ → ℝ := fun u => -(sargosQuarticPhase α γ (N*u)-y*(N*u))
    have hd (u : ℝ) : deriv φ u = -(N*(sargosQuarticSlope α γ (N*u)-y)) := by
      convert (((sargosQuarticPhase_hasDerivAt α γ (N*u)).comp u
        ((hasDerivAt_id u).const_mul N)).sub
        (((hasDerivAt_id u).const_mul N).const_mul y)).neg.deriv using 1
      ring
    have hφ : ContDiff ℝ ∞ φ :=
      (((contDiff_sargosQuarticPhase α γ).comp (contDiff_const.mul contDiff_id)).sub
        (contDiff_const.mul (contDiff_const.mul contDiff_id))).neg
    have hs : ∀ u ∈ Icc (l+η) (b-η), N*u ∈ Icc N (2*N) := by
      intro u hu
      constructor <;> nlinarith [hu.1,hu.2]
    have hm : AntitoneOn (deriv φ) (Icc (l+η) (b-η)) := by
      intro u hu v hv huv
      rw [hd,hd]
      exact neg_le_neg (mul_le_mul_of_nonneg_left
        (sub_le_sub_right ((sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
          (hs u hu) (hs v hv) (mul_le_mul_of_nonneg_left huv hN.le)) y) hN.le)
    have hg : (∀ u ∈ Icc (l+η) (b-η), N*lam ≤ deriv φ u) ∨
        (∀ u ∈ Icc (l+η) (b-η), deriv φ u ≤ -(N*lam)) := by
      rcases hgap with hp | hn
      · right
        intro u hu
        rw [hd]
        exact neg_le_neg (mul_le_mul_of_nonneg_left (hp u hu) hN.le)
      · left
        intro u hu
        rw [hd]
        have hh := mul_le_mul_of_nonneg_left (hn u hu) hN.le
        nlinarith
    have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := b) hη hab).fourierChar_of_closed_slope_gap
      hab (mul_pos hN hlam) isOpen_univ (subset_univ _)
      (fun _ _ => hφ.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)) hm hg
    have hsupp : Function.support (fun u : ℝ => (modelPhaseBufferedCutoff l b η u : ℂ)*
        (𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ)) ⊆ Ioc (l+η) (b-η) := by
      intro u hu
      have hχ : modelPhaseBufferedCutoff l b η u ≠ 0 := by
        intro hz
        exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])
      have hh := modelPhaseBufferedCutoff_support_open hη hχ
      exact ⟨hh.1,hh.2.le⟩
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
    have hi :
        (∫ u in (l+η)..(b-η), (modelPhaseBufferedCutoff l b η u : ℂ)*
          (𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ)) =
        conj (∫ u in (l+η)..(b-η), (modelPhaseBufferedCutoff l b η u : ℂ)*(𝐞 (φ u) : ℂ)) := by
      simp only [intervalIntegral.integral_of_le hab]
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [φ]
      rw [map_mul (starRingEnd ℂ),Complex.conj_ofReal,sargos_fourier_conj]
    rw [hi,Complex.norm_conj]
    apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
    field_simp
    ring
  · have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap hη (le_of_not_ge hab)
    simp only [hz,Complex.ofReal_zero,zero_mul,integral_zero,norm_zero,mul_zero]
    positivity

theorem sargosQuarticBufferedFourierMode_left_of_support {N α γ y l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+2*η ≤ b)
    (hy : y < sargosQuarticSlope α γ (N*(l+η))) :
    ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
      4/((sargosQuarticSlope α γ (N*(l+η))-y)*Real.pi) := by
  apply sargosQuarticBufferedFourierMode_of_slope_gap hN hα hγ hη hl hb (sub_pos.mpr hy)
  left
  intro u hu
  have ha : N*(l+η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hx : N*u ∈ Icc N (2*N) := by constructor <;> nlinarith [hu.1,hu.2]
  exact sub_le_sub_right ((sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
    ha hx (mul_le_mul_of_nonneg_left hu.1 hN.le)) y

theorem sargosQuarticBufferedFourierMode_right_of_support {N α γ y l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+2*η ≤ b)
    (hy : sargosQuarticSlope α γ (N*(b-η)) < y) :
    ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
      4/((y-sargosQuarticSlope α γ (N*(b-η)))*Real.pi) := by
  apply sargosQuarticBufferedFourierMode_of_slope_gap hN hα hγ hη hl hb (sub_pos.mpr hy)
  right
  intro u hu
  have ha : N*(b-η) ∈ Icc N (2*N) := by constructor <;> nlinarith
  have hx : N*u ∈ Icc N (2*N) := by constructor <;> nlinarith [hu.1,hu.2]
  have hm := (sargosQuarticSlope_strictMonoOn hN hα hγ).monotoneOn
    hx ha (mul_le_mul_of_nonneg_left hu.2 hN.le)
  linarith

end TaoTrudgianYang2025

