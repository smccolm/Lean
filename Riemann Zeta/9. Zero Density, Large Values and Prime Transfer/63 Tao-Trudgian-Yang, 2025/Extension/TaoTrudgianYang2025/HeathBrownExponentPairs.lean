import TaoTrudgianYang2025.HeathBrownPairLocalBound
import TaoTrudgianYang2025.HeathBrownPairTriangle
import TaoTrudgianYang2025.BetaHalfDuality
import TaoTrudgianYang2025.HeathBrownDerivative

/-!
# Actual Heath--Brown family from the native derivative theorem

The integer derivative order is selected from the physical logarithmic ratio
tau = 1/alpha, not supplied as an optimization certificate.
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem heathBrownBetaBound_reciprocal_scale {j : ℕ} (hj : 3 ≤ j)
    {α τ : ℝ} (hτ : 0 < τ) (hτα : τ*α = 1) :
    τ*heathBrownBetaBound j α =
      1+max ((τ-(j:ℝ))/((j:ℝ)*(j-1)))
        (max (-1/((j:ℝ)*(j-1))) (-2*τ/((j:ℝ)^2*(j-1)))) := by
  have hjr : (3:ℝ) ≤ j := by exact_mod_cast hj
  have h0 : (j:ℝ) ≠ 0 := by linarith
  have h1 : (j:ℝ)-1 ≠ 0 := by linarith
  have hf : τ*((1-(j:ℝ)*α)/((j:ℝ)*(j-1))) =
      (τ-(j:ℝ))/((j:ℝ)*(j-1)) := by
    calc
      _ = (τ-(j:ℝ)*(τ*α))/((j:ℝ)*(j-1)) := by ring
      _ = _ := by rw [hτα]; ring
  have hs : τ*(-α/((j:ℝ)*(j-1))) = -1/((j:ℝ)*(j-1)) := by
    calc
      _ = -(τ*α)/((j:ℝ)*(j-1)) := by ring
      _ = _ := by rw [hτα]
  have ht : τ*(-2*α/((j:ℝ)*(j-1))-2*(1-(j:ℝ)*α)/((j:ℝ)^2*(j-1))) =
      -2*τ/((j:ℝ)^2*(j-1)) := by
    calc
      _ = -2*(τ*α)/((j:ℝ)*(j-1))-2*(τ-(j:ℝ)*(τ*α))/((j:ℝ)^2*(j-1)) := by ring
      _ = -2/((j:ℝ)*(j-1))-2*(τ-(j:ℝ))/((j:ℝ)^2*(j-1)) := by rw [hτα]; ring
      _ = _ := by field_simp; ring
  unfold heathBrownBetaBound
  rw [mul_add,hτα,mul_max_of_nonneg _ _ hτ.le,mul_max_of_nonneg _ _ hτ.le,hf,hs,ht]

theorem heathBrownPairSecant_target {r α τ : ℝ}
    (hr : 3 ≤ r) (hτα : τ*α = 1) :
    τ*exponentPairLine (heathBrownPairK r) (heathBrownPairL r) α =
      1+heathBrownPairSecant r τ := by
  rw [heathBrownPairSecant,heathBrownPairIntercept_eq hr]
  unfold exponentPairLine
  calc
    _ = τ*heathBrownPairK r+(heathBrownPairL r-heathBrownPairK r)*(τ*α) := by ring
    _ = _ := by rw [hτα]; ring

theorem exponentSumGrowthExponent_le_heathBrownPair_half {k : ℕ}
    (hk : 3 ≤ k) {α : ℝ≥0} (hαhalf : (α:ℝ) ≤ 1/2) :
    exponentSumGrowthExponent α ≤ exponentPairLine (heathBrownPairK k) (heathBrownPairL k) α := by
  have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
  by_cases hα : 0 < (α:ℝ)
  · let τ : ℝ := 1/(α:ℝ)
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hτα : τ*(α:ℝ) = 1 := by dsimp [τ]; field_simp
    have hτ2 : 2 ≤ τ := by
      apply (le_div_iff₀ hα).mpr
      linarith
    obtain ⟨j,hj,hl,hu⟩ := exists_heathBrownPair_segment hτ2
    have hjr : (3:ℝ) ≤ j := by exact_mod_cast hj
    have hb := exponentSumGrowthExponent_le_iff_nonAsymptotic.mpr
      (isExponentSumBoundNonAsymptotic_heathBrown hj hα)
    have hscaled := mul_le_mul_of_nonneg_left hb hτ.le
    rw [heathBrownBetaBound_reciprocal_scale hj hτ hτα] at hscaled
    have hlocal := heathBrownPairSecant_derivative_max hjr hl hu
    have hglobal := heathBrownPairSecant_segment_le hj hk hl hu
    have htarget := heathBrownPairSecant_target hkr hτα
    exact le_of_mul_le_mul_left (a:=τ) (by linarith) hτ
  · have hz : α = 0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hα) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    simpa only [exponentPairLine,NNReal.coe_zero,mul_zero,add_zero] using
      (heathBrownPairK_pos hkr).le

theorem exponentPair_heathBrown {k : ℕ} (hk : 3 ≤ k) :
    ExponentPair (2/(((k:ℝ)-1)^2*((k:ℝ)+2)))
      (1-(3*(k:ℝ)-2)/((k:ℝ)*((k:ℝ)-1)*((k:ℝ)+2))) := by
  have hkr : (3:ℝ) ≤ k := by exact_mod_cast hk
  exact exponentPair_of_beta_bound_half (heathBrownPair_inTriangle hkr)
    (heathBrownPair_slope hkr) (fun _ hα => exponentSumGrowthExponent_le_heathBrownPair_half hk hα)

end TaoTrudgianYang2025
