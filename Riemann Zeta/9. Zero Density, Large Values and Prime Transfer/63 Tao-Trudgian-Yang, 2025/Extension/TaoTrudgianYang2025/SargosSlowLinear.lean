import TaoTrudgianYang2025.SargosSlowRegularity

/-! Genuine parameter-dependent linear phases, including nonmeasurable families. -/

noncomputable section

open GafniTao MeasureTheory Set
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosSlowQuarticPrefix_zero_phase (N H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosSlowQuarticPrefix N H z α γ (fun _ => 0) = sargosQuarticPrefix N H z α γ := by
  simp only [sargosSlowQuarticPrefix,sargosQuarticPrefix,add_zero]

theorem sargosSlowQuarticMaximum_zero_phase (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosSlowQuarticMaximum N z α γ (fun _ => 0) = sargosQuarticPrefixMaximum N z α γ := by
  unfold sargosSlowQuarticMaximum sargosQuarticPrefixMaximum
  apply Finset.sup'_congr _ rfl
  intro H hH
  rw [sargosSlowQuarticPrefix_zero_phase]

theorem sargos_linear_phase_hasDerivWithin (N : ℕ) (u x : ℝ) :
    HasDerivWithinAt (fun t : ℝ => u*t/N) (u/N) (Icc (N : ℝ) (2*N)) x := by
  simpa only [mul_one] using
    (((hasDerivAt_id x).const_mul u).div_const (N : ℝ)).hasDerivWithinAt

theorem sargos_linear_phase_derivative_bound {N : ℕ} (hN : 1 ≤ N)
    {u K : ℝ} (hu : |u| ≤ K) : ‖u/(N : ℝ)‖ ≤ K/N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hNp]
  exact div_le_div_of_nonneg_right hu hNp.le

theorem sargosSlowQuartic_linear_upper_fourth_moment {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ : ℝ} (hK : 0 ≤ K) (hΔ : 1/(N : ℝ) ≤ Δ)
    (u : ℝ → ℝ → ℝ)
    (hu : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3), |u α γ| ≤ K) :
    sargosUpperIntegral
      ((volume.restrict (Icc (0 : ℝ) Δ)).prod
        (volume.restrict (Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3))))
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z p.1 p.2 (fun x => u p.1 p.2*x/N))^4)) ≤
      ENNReal.ofReal ((1+2*Real.pi*K)^4*
        (10616832*Δ/(N : ℝ)*(1+Real.log N)^5)) := by
  apply sargosSlowQuartic_upper_fourth_moment hN z hz hK hΔ
    (fun α γ x => u α γ*x/N) (fun α γ _ => u α γ/N)
  · intro α hα γ hγ x hx
    exact sargos_linear_phase_hasDerivWithin N (u α γ) x
  · intro α hα γ hγ x hx
    exact sargos_linear_phase_derivative_bound hN (hu α hα γ hγ)

theorem sargosSlowQuartic_linear_fourth_moment {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ : ℝ} (hK : 0 ≤ K) (hΔ : 1/(N : ℝ) ≤ Δ)
    (u : ℝ → ℝ → ℝ) (hc : Continuous (fun p : ℝ × ℝ => u p.1 p.2))
    (hu : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3), |u α γ| ≤ K) :
    (∫ α in Icc (0 : ℝ) Δ,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosSlowQuarticMaximum N z α γ (fun x => u α γ*x/N))^4) ≤
      (1+2*Real.pi*K)^4*(10616832*Δ/(N : ℝ)*(1+Real.log N)^5) := by
  apply sargosSlowQuartic_fourth_moment hN z hz hK hΔ
    (fun α γ x => u α γ*x/N) (fun α γ _ => u α γ/N)
  · intro α hα γ hγ x hx
    exact sargos_linear_phase_hasDerivWithin N (u α γ) x
  · intro α hα γ hγ x hx
    exact sargos_linear_phase_derivative_bound hN (hu α hα γ hγ)
  · exact ((continuous_sargosSlowQuarticMaximum N z (fun α γ x => u α γ*x/N)
      (fun n => (hc.mul continuous_const).div_const _)).pow 4).aestronglyMeasurable

end TaoTrudgianYang2025
