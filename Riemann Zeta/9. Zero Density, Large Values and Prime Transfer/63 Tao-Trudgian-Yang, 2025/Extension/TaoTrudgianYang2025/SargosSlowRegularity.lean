import TaoTrudgianYang2025.SargosSlowMoment

/-! Measurable slow phases: actual integrability and the iterated fourth moment. -/

noncomputable section

open GafniTao MeasureTheory Set Filter

namespace TaoTrudgianYang2025

theorem continuous_sargosSlowQuarticMaximum (N : ℕ) (z : ℤ → ℂ)
    (φ : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ n : ℤ, Continuous (fun p : ℝ × ℝ => φ p.1 p.2 n)) :
    Continuous (fun p : ℝ × ℝ => sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2)) := by
  unfold sargosSlowQuarticMaximum
  apply Continuous.finset_sup'_apply
  intro H hH
  unfold sargosSlowQuarticPrefix fordAdditiveCharacter
  apply Continuous.norm
  apply continuous_finsetSum
  intro n hn
  fun_prop

theorem integrable_sargosSlowQuarticFourth {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    Integrable
      (fun p : ℝ × ℝ => (sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hi := (integrable_sargosQuarticPrefixMaximum_rectangle N z a b c d).const_mul
    ((1+2*Real.pi*K)^4)
  apply hi.mono' hm
  filter_upwards [sargosSlowQuartic_pow_four_le_ae hN z hK a b c d φ φ' hφ hφ'] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact hp

theorem sargosSlowQuartic_fourth_moment {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ : ℝ} (hK : 0 ≤ K) (hΔ : 1/(N : ℝ) ≤ Δ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
      ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4)
      ((volume.restrict (Icc (0 : ℝ) Δ)).prod
        (volume.restrict (Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3))))) :
    (∫ α in Icc (0 : ℝ) Δ,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosSlowQuarticMaximum N z α γ (φ α γ))^4) ≤
      (1+2*Real.pi*K)^4*(10616832*Δ/(N : ℝ)*(1+Real.log N)^5) := by
  have hi := integrable_sargosSlowQuarticFourth hN z hK 0 Δ _ _ φ φ' hφ hφ' hm
  have hu := sargosSlowQuartic_upper_fourth_moment hN z hz hK hΔ φ φ' hφ hφ'
  rw [sargosUpperIntegral_ofReal_eq_integral hi
    (Eventually.of_forall (fun p => by positivity)),integral_prod _ hi] at hu
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hΔp : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  have hlog := Real.log_nonneg hNr
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hu

end TaoTrudgianYang2025
