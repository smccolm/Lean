import TaoTrudgianYang2025.SargosInitialRegularity

/-! Integration of the literal dyadic decomposition and the completed source moment. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuartic_sixth_moment (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ z : ℤ → ℂ,
      (∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1) →
      ∀ lambda : ℝ, 0 < lambda → ∀ c d : ℝ,
      (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosQuarticSum N z α γ‖^6) ≤
        C*(lambda*(N:ℝ)^(3+ε)+(N:ℝ)^ε) := by
  obtain ⟨C,hC,h⟩ := sargosQuartic_maximal_sixth_moment ε hε
  refine ⟨C,hC,?_⟩
  intro N hN z hz lambda hlambda c d
  refine le_trans ?_ (h N hN z hz lambda hlambda c d)
  apply integral_mono
    (integrable_sargosQuarticNormPower_outer N 6 z c (c+1) d (d+lambda))
    (integrable_sargosQuarticMaximumPower_outer N 6 z c (c+1) d (d+lambda))
  intro α
  apply integral_mono
    (integrable_sargosQuarticNormPower_inner N 6 z α d (d+lambda))
    (integrable_sargosQuarticMaximumPower_inner N 6 z α d (d+lambda))
  intro γ
  apply pow_le_pow_left₀ (norm_nonneg _) _ 6
  rw [← sargosQuarticPrefix_full]
  exact norm_sargosQuarticPrefix_le_maximum z α γ le_rfl

theorem sargosInitialQuartic_dyadic_integral (K : ℕ) (z : ℤ → ℂ)
    (c d lambda : ℝ) :
    (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      ‖sargosInitialQuarticSum (2^(K+1)) z α γ‖^6) ≤
      32*((∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        ‖sargosInitialQuarticSum 2 z α γ‖^6)+
        (K:ℝ)^5*∑ i ∈ Finset.range K,
          ∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
            ‖sargosQuarticSum (2^(i+1)) z α γ‖^6) := by
  let μ := (volume.restrict (Icc c (c+1))).prod (volume.restrict (Icc d (d+lambda)))
  have hP := integrable_sargosInitialQuarticNormPower_rectangle (2^(K+1)) 6 z c (c+1) d (d+lambda)
  have h₂ := integrable_sargosInitialQuarticNormPower_rectangle 2 6 z c (c+1) d (d+lambda)
  have hi (i : ℕ) := integrable_sargosQuarticNormPower_rectangle (2^(i+1)) 6 z c (c+1) d (d+lambda)
  have hs := integrable_finsetSum (Finset.range K) (fun i _ => hi i)
  calc
    _ = ∫ t : ℝ × ℝ, ‖sargosInitialQuarticSum (2^(K+1)) z t.1 t.2‖^6 ∂μ :=
      (integral_prod _ hP).symm
    _ ≤ ∫ t : ℝ × ℝ, 32*(‖sargosInitialQuarticSum 2 z t.1 t.2‖^6+
        (K:ℝ)^5*∑ i ∈ Finset.range K, ‖sargosQuarticSum (2^(i+1)) z t.1 t.2‖^6) ∂μ := by
      apply integral_mono hP ((h₂.add (hs.const_mul ((K:ℝ)^5))).const_mul 32)
      intro t
      exact sargosInitialQuarticSum_dyadic_sixth K z t.1 t.2
    _ = _ := by
      rw [integral_const_mul,integral_add h₂ (hs.const_mul ((K:ℝ)^5)),
        integral_const_mul,integral_finsetSum (Finset.range K) (fun i _ => hi i),
        integral_prod _ h₂]
      simp_rw [integral_prod _ (hi _)]

end TaoTrudgianYang2025

