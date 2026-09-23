import TaoTrudgianYang2025.SargosQuarticInteriorStationary
import TaoTrudgianYang2025.PhaseWeightedCurvature

/-! Width-independent curvature bounds for every actual quartic Fourier frequency. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargosQuarticBuffered_normalized_curvature {N α γ y l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) :
    ‖∫ u : ℝ, (modelPhaseBufferedCutoff l b η u : ℂ)*
      (𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ)‖ ≤
      4*(2/Real.pi+2)/Real.sqrt (α*N^2) := by
  by_cases hab : l+η ≤ b-η
  · let φ : ℝ → ℝ := fun u => -(sargosQuarticPhase α γ (N*u)-y*(N*u))
    have hd (u : ℝ) : HasDerivAt φ (-(N*(sargosQuarticSlope α γ (N*u)-y))) u := by
      convert (((sargosQuarticPhase_hasDerivAt α γ (N*u)).comp u
        ((hasDerivAt_id u).const_mul N)).sub
        (((hasDerivAt_id u).const_mul N).const_mul y)).neg using 1
      ring
    have he : deriv φ = fun u => -(N*(sargosQuarticSlope α γ (N*u)-y)) :=
      funext fun u => (hd u).deriv
    have hdd (u : ℝ) : deriv (deriv φ) u = -(N^2*(2*α+12*γ*(N*u)^2)) := by
      rw [he]
      convert ((((sargosQuarticSlope_hasDerivAt α γ (N*u)).comp u
        ((hasDerivAt_id u).const_mul N)).sub_const y).const_mul N).neg.deriv using 1
      ring
    have hφ : ContDiff ℝ ∞ φ :=
      (((contDiff_sargosQuarticPhase α γ).comp (contDiff_const.mul contDiff_id)).sub
        (contDiff_const.mul (contDiff_const.mul contDiff_id))).neg
    have hcurv : ∀ u ∈ Ioo (1 : ℝ) 2, deriv (deriv φ) u ≤ -(α*N^2) := by
      intro u hu
      have hxu : N*u ∈ Icc N (2*N) := by
        constructor <;> nlinarith [hu.1,hu.2]
      have hc := (sargosQuarticPhase_curvature hN hα hγ hxu).1
      rw [hdd]
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg N)]
    have hs : Icc (l+η) (b-η) ⊆ Ioo (1 : ℝ) 2 := by
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := b) hη hab).fourierChar_of_negative_curvature
      hab (by positivity : 0 < α*N^2) isOpen_Ioo hs
      (fun _ _ => hφ.contDiffAt.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞)) hcurv
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
    convert h using 1
    norm_num
  · have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap hη (le_of_not_ge hab)
    simp only [hz,Complex.ofReal_zero,zero_mul,integral_zero,norm_zero]
    positivity

theorem sargosQuarticBufferedFourierMode_curvature {N α γ y l b η : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) :
    ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
      4*(2/Real.pi+2)/Real.sqrt α := by
  rw [sargosQuarticFourierMode_eq_normalized _ hN,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN]
  have h := sargosQuarticBuffered_normalized_curvature (y := y) hN hα hγ hη hl hb
  apply (mul_le_mul_of_nonneg_left h hN.le).trans_eq
  rw [Real.sqrt_mul hα.le,Real.sqrt_sq_eq_abs,abs_of_pos hN]
  field_simp

theorem sargosQuarticStationaryMainTerm_norm_bound {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    ‖sargosQuarticStationaryMainTerm N α γ y‖ ≤ 1/Real.sqrt α := by
  have hw := sargosQuarticInverseSlope_mem hN hα hγ hy
  have hc := (sargosQuarticPhase_curvature hN hα hγ ⟨hw.1.le,hw.2.le⟩).1
  have ha : α ≤ 2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 := by linarith
  simp only [sargosQuarticStationaryMainTerm,norm_div,Circle.norm_coe,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hα) (Real.sqrt_le_sqrt ha)

theorem sargosQuarticBufferedFourierMode_uniform_curvature :
    ∃ C : ℝ, 0 < C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η →
      ∀ (N α γ y : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤ C/Real.sqrt α := by
  refine ⟨4*(2/Real.pi+2),by positivity,?_⟩
  intro l b η hl hb hη N α γ y hN hα hγ
  exact sargosQuarticBufferedFourierMode_curvature hN hα hγ hη hl hb

end TaoTrudgianYang2025

