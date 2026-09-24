import TaoTrudgianYang2025.HeathBrownSharpLocal
import TaoTrudgianYang2025.JutilaLargeValues
import TaoTrudgianYang2025.LargeValueSubdivisionBounds

/-!
# The classical Heath--Brown optimized large-value bound

The high-sigma branch is proved from actual sharp Gram sums and the zeta
twelfth moment. Jutila with k=2 and one-separation cover the lower strip.
The resulting expression is the exact printed `hb-opt` maximum.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem heathBrown_largeValueBound {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ (max (2-2*σ) (10+τ-13*σ)) := by
  by_cases hlo : σ ≤ 10/13
  · exact (obvious_largeValueBound σ hτ).mono
      ((show τ ≤ 10+τ-13*σ by linarith).trans (le_max_right _ _))
  by_cases hmid : σ ≤ 7/8
  · apply (jutila_largeValueBound 2 (by norm_num) hσ hσ1 hτ).mono
    unfold jutilaLargeValueExponent
    norm_num only [Nat.cast_ofNat,div_self (by norm_num : (2 : ℝ) ≠ 0)]
    apply max_le (le_max_left _ _)
    apply max_le
    · apply le_trans _ (le_max_right (2-2*σ) (10+τ-13*σ))
      linarith
    · apply le_trans _ (le_max_right (2-2*σ) (10+τ-13*σ))
      linarith
  have hhigh : 7/8 ≤ σ := le_of_not_ge hmid
  have hlocal : IsLargeValueBound σ (11*σ-8) (2-2*σ) := by
    have hh := heathBrown_sharp_local_largeValueBound hhigh
      (show 3/2 ≤ 11*σ-8 by linarith)
    simpa only [show 18+2*(11*σ-8)-24*σ = 2-2*σ by ring,max_self] using hh
  by_cases ht : τ ≤ 11*σ-8
  · exact (hlocal.of_height_le ht).mono (le_max_left _ _)
  · have hh := hlocal.subdivision (le_of_not_ge ht)
    apply hh.mono
    exact (show (2-2*σ)+(τ-(11*σ-8)) = 10+τ-13*σ by ring).le.trans
      (le_max_right _ _)

theorem largeValueExponent_le_heathBrown {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) :
    largeValueExponent σ τ ≤ (max (2-2*σ) (10+τ-13*σ) : ℝ) :=
  largeValueExponent_le_of_bound (heathBrown_largeValueBound hσ hσ1 hτ)

theorem zetaLargeValueExponent_le_heathBrown {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) :
    zetaLargeValueExponent σ τ ≤ (max (2-2*σ) (10+τ-13*σ) : ℝ) :=
  zetaLargeValueExponent_le_of_bound (heathBrown_largeValueBound hσ hσ1 hτ).toZeta

end TaoTrudgianYang2025
