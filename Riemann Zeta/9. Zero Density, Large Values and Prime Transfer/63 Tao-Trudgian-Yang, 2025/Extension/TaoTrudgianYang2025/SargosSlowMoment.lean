import TaoTrudgianYang2025.SargosSlowPrefix
import TaoTrudgianYang2025.SargosUpperIntegral

/-!
# Fourth moment with an arbitrary parameter-dependent slow phase

The nonmeasurable case uses a genuine upper integral of the nonnegative
integrand over the physical rectangle. The derivative hypotheses are
local to that rectangle and to the actual source interval.
-/

noncomputable section

open GafniTao MeasureTheory Set Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosSlowQuartic_pow_four_le_ae {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N) :
    ∀ᵐ p ∂((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))),
      (sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4 ≤
        (1+2*Real.pi*K)^4*(sargosQuarticPrefixMaximum N z p.1 p.2)^4 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  exact sargosSlowQuarticMaximum_pow_four_le hN z p.1 p.2 hK
    (hφ p.1 hp.1 p.2 hp.2) (hφ' p.1 hp.1 p.2 hp.2)

theorem sargosSlowQuartic_upper_rectangle_le {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) {K : ℝ} (hK : 0 ≤ K) (a b c d : ℝ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc a b, ∀ γ ∈ Icc c d, ∀ x ∈ Icc (N : ℝ) (2*N),
      ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)))
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4)) ≤
      ENNReal.ofReal ((1+2*Real.pi*K)^4*
        (∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^4)) := by
  have hi := integrable_sargosQuarticPrefixMaximum_rectangle N z a b c d
  have h := sargosUpperIntegral_ofReal_le_integral (hi.const_mul ((1+2*Real.pi*K)^4))
    (Eventually.of_forall (fun p => by positivity))
    (sargosSlowQuartic_pow_four_le_ae hN z hK a b c d φ φ' hφ hφ')
  rw [integral_const_mul,integral_prod _ hi] at h
  exact h

theorem sargosSlowQuartic_upper_fourth_moment {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {K Δ : ℝ} (hK : 0 ≤ K) (hΔ : 1/(N : ℝ) ≤ Δ)
    (φ φ' : ℝ → ℝ → ℝ → ℝ)
    (hφ : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
      ∀ x ∈ Icc (N : ℝ) (2*N),
      HasDerivWithinAt (φ α γ) (φ' α γ x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ α ∈ Icc (0 : ℝ) Δ,
      ∀ γ ∈ Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
      ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' α γ x‖ ≤ K/N) :
    sargosUpperIntegral
      ((volume.restrict (Icc (0 : ℝ) Δ)).prod
        (volume.restrict (Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3))))
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum N z p.1 p.2 (φ p.1 p.2))^4)) ≤
      ENNReal.ofReal ((1+2*Real.pi*K)^4*
        (10616832*Δ/(N : ℝ)*(1+Real.log N)^5)) := by
  apply (sargosSlowQuartic_upper_rectangle_le hN z hK 0 Δ _ _ φ φ' hφ hφ').trans
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
    (sargosQuartic_maximal_fourth_moment hN z hz hΔ) (by positivity))

end TaoTrudgianYang2025
