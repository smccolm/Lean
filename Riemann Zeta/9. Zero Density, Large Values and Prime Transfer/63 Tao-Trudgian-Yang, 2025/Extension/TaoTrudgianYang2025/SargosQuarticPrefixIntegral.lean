import TaoTrudgianYang2025.SargosQuarticMomentRegularity

/-! Integrating the common prefix majorant on the actual source rectangle. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticPrefix_inner_le_completed {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (α c d : ℝ) :
    (∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^4) ≤
      (∑ k : ZMod N, sargosPrefixMajorant k)^3*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) := by
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  have hi (k : ZMod N) : IntegrableOn
      (fun γ : ℝ => sargosPrefixMajorant k*
        ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4) (Icc c d) :=
    (integrable_sargosQuarticNormFour_inner N (sargosQuarticTwist z k) α c d).const_mul _
  have hs : IntegrableOn (fun γ : ℝ => ∑ k : ZMod N, sargosPrefixMajorant k*
      ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4) (Icc c d) :=
    integrable_finsetSum _ (fun k hk => hi k)
  calc
    _ ≤ ∫ γ in Icc c d, B^3*(∑ k : ZMod N, sargosPrefixMajorant k*
        ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4) := by
      apply integral_mono (integrable_sargosQuarticPrefixMaximum_inner N z α c d)
        (hs.const_mul (B^3))
      intro γ
      exact (sargosQuarticPrefixMaximum_pow_four_le (N := N) z α γ).trans_eq
        (sargosQuartic_fourier_majorant_eq (N := N) z α γ)
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun k hk => hi k)]
      simp only [integral_const_mul,B]

theorem sargosQuarticPrefix_rectangle_le_completed {N : ℕ} [NeZero N]
    (z : ℤ → ℂ) (a b c d : ℝ) :
    (∫ α in Icc a b, ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^4) ≤
      (∑ k : ZMod N, sargosPrefixMajorant k)^3*
        (∑ k : ZMod N, sargosPrefixMajorant k*
          (∫ α in Icc a b, ∫ γ in Icc c d,
            ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) := by
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  have hi (k : ZMod N) : IntegrableOn
      (fun α : ℝ => sargosPrefixMajorant k*
        (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) (Icc a b) :=
    (integrable_sargosQuarticNormFour_outer N (sargosQuarticTwist z k) a b c d).const_mul _
  have hs : IntegrableOn (fun α : ℝ => ∑ k : ZMod N, sargosPrefixMajorant k*
      (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) (Icc a b) :=
    integrable_finsetSum _ (fun k hk => hi k)
  calc
    _ ≤ ∫ α in Icc a b, B^3*(∑ k : ZMod N, sargosPrefixMajorant k*
        (∫ γ in Icc c d, ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) := by
      apply integral_mono (integrable_sargosQuarticPrefixMaximum_outer N z a b c d)
        (hs.const_mul (B^3))
      intro α
      exact sargosQuarticPrefix_inner_le_completed (N := N) z α c d
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum Finset.univ (fun k hk => hi k)]
      simp only [integral_const_mul,B]

end TaoTrudgianYang2025
