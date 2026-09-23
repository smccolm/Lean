import TaoTrudgianYang2025.SargosWeightedPowers
import TaoTrudgianYang2025.SargosPowerRegularity

/-! Completion for every positive integer power of the actual source prefix maximum. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticMaximum_pow_succ_le_completed {N : ℕ} [NeZero N]
    (p : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    (sargosQuarticPrefixMaximum N z α γ)^(p+1) ≤
      (∑ k : ZMod N, sargosPrefixMajorant k)^p*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1)) := by
  rw [sargosQuarticPrefixMaximum_eq_finite]
  have h := sargosFinitePrefixMaximum_pow_succ_le p (sargosQuarticSample (N := N) z α γ)
  simpa only [sargosFourierPowerMajorant,sargosQuarticSample_dft] using h

theorem sargosQuarticMaximum_power_inner_le_completed {N : ℕ} [NeZero N]
    (p : ℕ) (z : ℤ → ℂ) (α c d : ℝ) :
    (∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^(p+1)) ≤
      (∑ k : ZMod N, sargosPrefixMajorant k)^p*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1))) := by
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  have hi (k : ZMod N) : IntegrableOn
      (fun γ : ℝ => sargosPrefixMajorant k*
        ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1)) (Icc c d) :=
    (integrable_sargosQuarticNormPower_inner N (p+1) (sargosQuarticTwist z k) α c d).const_mul _
  have hs : IntegrableOn (fun γ : ℝ => ∑ k : ZMod N, sargosPrefixMajorant k*
      ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1)) (Icc c d) :=
    integrable_finsetSum _ (fun k hk => hi k)
  calc
    _ ≤ ∫ γ in Icc c d, B^p*(∑ k : ZMod N, sargosPrefixMajorant k*
        ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1)) := by
      apply integral_mono (integrable_sargosQuarticMaximumPower_inner N (p+1) z α c d)
        (hs.const_mul (B^p))
      intro γ
      exact sargosQuarticMaximum_pow_succ_le_completed (N := N) p z α γ
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun k hk => hi k)]
      simp only [integral_const_mul,B]

theorem sargosQuarticMaximum_power_rectangle_le_completed {N : ℕ} [NeZero N]
    (p : ℕ) (z : ℤ → ℂ) (a b c d : ℝ) :
    (∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^(p+1)) ≤
      (∑ k : ZMod N, sargosPrefixMajorant k)^p*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          (∫ α in Icc a b, ∫ γ in Icc c d,
            ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1))) := by
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  have hi (k : ZMod N) : IntegrableOn
      (fun α : ℝ => sargosPrefixMajorant k*
        (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1))) (Icc a b) :=
    (integrable_sargosQuarticNormPower_outer N (p+1) (sargosQuarticTwist z k) a b c d).const_mul _
  have hs : IntegrableOn (fun α : ℝ => ∑ k : ZMod N, sargosPrefixMajorant k*
      (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1))) (Icc a b) :=
    integrable_finsetSum _ (fun k hk => hi k)
  calc
    _ ≤ ∫ α in Icc a b, B^p*(∑ k : ZMod N, sargosPrefixMajorant k*
        (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^(p+1))) := by
      apply integral_mono (integrable_sargosQuarticMaximumPower_outer N (p+1) z a b c d)
        (hs.const_mul (B^p))
      intro α
      exact sargosQuarticMaximum_power_inner_le_completed (N := N) p z α c d
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun k hk => hi k)]
      simp only [integral_const_mul,B]

end TaoTrudgianYang2025

