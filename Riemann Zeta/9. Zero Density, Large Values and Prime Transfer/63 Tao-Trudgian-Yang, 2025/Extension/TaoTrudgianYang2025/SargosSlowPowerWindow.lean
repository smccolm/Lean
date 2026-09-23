import TaoTrudgianYang2025.SargosSlowRegularity
import TaoTrudgianYang2025.SargosPowerRegularity

/-! Arbitrary slow-phase powers, with a genuine upper integral when parameters are nonmeasurable. -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosSlowQuartic_power_le_ae {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N) :
    ∀ᵐ t ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))),
      (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^p ≤
        (1+2*Real.pi*K)^p*(sargosQuarticPrefixMaximum N z t.1 t.2)^p := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with t ht
  have h := pow_le_pow_left₀ (sargosSlowQuarticMaximum_nonneg N z t.1 t.2 (φ t.1 t.2))
    (sargosSlowQuarticMaximum_le hN z t.1 t.2 hK
      (hφ t.1 ht.1 t.2 ht.2) (hφ' t.1 ht.1 t.2 ht.2)) p
  simpa only [mul_pow] using h

theorem sargosSlowQuartic_upper_power_rectangle_le {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))
      (fun t : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^p)) ≤
      ENNReal.ofReal ((1+2*Real.pi*K)^p*
        (∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^p)) := by
  have hi := integrable_sargosQuarticMaximumPower_rectangle N p z a b c d
  have hn (t : ℝ × ℝ) :
      0 ≤ (1+2*Real.pi*K)^p*(sargosQuarticPrefixMaximum N z t.1 t.2)^p :=
    mul_nonneg (pow_nonneg (by positivity) p)
      (pow_nonneg (sargosQuarticPrefixMaximum_nonneg N z t.1 t.2) p)
  have h := sargosUpperIntegral_ofReal_le_integral (hi.const_mul ((1+2*Real.pi*K)^p))
    (Eventually.of_forall hn)
    (sargosSlowQuartic_power_le_ae hN p z hK a b c d φ φ' hφ hφ')
  rw [integral_const_mul,integral_prod _ hi] at h
  exact h

theorem integrable_sargosSlowQuarticPower {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    Integrable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hi := (integrable_sargosQuarticMaximumPower_rectangle N p z a b c d).const_mul
    ((1+2*Real.pi*K)^p)
  apply hi.mono' hm
  filter_upwards [sargosSlowQuartic_power_le_ae hN p z hK a b c d φ φ' hφ hφ'] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg
    (pow_nonneg (sargosSlowQuarticMaximum_nonneg N z t.1 t.2 (φ t.1 t.2)) p)]
  exact ht

theorem sargosSlowQuartic_power_rectangle_le {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N)
    (hm : AEStronglyMeasurable
      (fun t : ℝ × ℝ => (sargosSlowQuarticMaximum N z t.1 t.2 (φ t.1 t.2))^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))) :
    (∫ α in Icc a b, ∫ γ in Icc c d,
      (sargosSlowQuarticMaximum N z α γ (φ α γ))^p) ≤
      (1+2*Real.pi*K)^p*
        (∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^p) := by
  have hi := integrable_sargosSlowQuarticPower hN p z hK a b c d φ φ' hφ hφ' hm
  have hj := integrable_sargosQuarticMaximumPower_rectangle N p z a b c d
  have h := integral_mono_ae hi (hj.const_mul ((1+2*Real.pi*K)^p))
    (sargosSlowQuartic_power_le_ae hN p z hK a b c d φ φ' hφ hφ')
  rwa [integral_const_mul,integral_prod _ hi,integral_prod _ hj] at h

end TaoTrudgianYang2025

