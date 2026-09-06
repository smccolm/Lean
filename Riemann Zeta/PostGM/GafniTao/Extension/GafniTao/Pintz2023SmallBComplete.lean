import GafniTao.Pintz2023GramCutoffAbsorption

/-!
# Pintz (2023), complete small-`B_h` off-diagonal Gram bound

This theorem assembles the literal `n = 1` term, equations (4.23) and
(4.21), the integer `A ceil(log A)^2` cutoff, and the complete geometric
tail.  The output is the uniform off-diagonal power saving needed by the
Halasz consumer.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The complete small-`B_h` branch of Pintz's estimate following (4.23).
All endpoint and logarithmic losses are included in the factor four. -/
theorem eventually_pintz2023_smallB_complete_gram_native
    (r : ℕ) (eta epsilon : ℝ) (hr : 3 ≤ r)
    (heta : 0 ≤ eta) (hepsilon : 0 < epsilon)
    (hepsilonUpper : 3 * epsilon ≤ 1)
    (hTarget : 2 * epsilon ≤ 4 * eta) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ᶠ A : ℕ in atTop, ∀ (xi t T : ℝ),
        0 ≤ xi →
        0 ≤ 1 - (xi + 4 * eta) →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
        1 ≤ t → t ≤ T → 1 ≤ T →
        pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ) →
        (A : ℝ) ≤ t ^ (19 / (10 * (r : ℝ))) →
        ‖pintz2023SmoothedZetaSum A
            (((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          4 * (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
  obtain ⟨C₀, hC₀, hLow⟩ :=
    pintz2023_low_block_equation423_raw_native
      r epsilon 4 hr hepsilon (by norm_num)
  obtain ⟨C₁, hC₁, hMiddle⟩ :=
    pintz2023_middle_block_equation421_native
      r epsilon 4 hr hepsilon (by norm_num)
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  have hrPos : 0 < r := by omega
  have hCutoffScale := eventually_pintz2023GramCutoff_le_smallB_scale r hrPos
  have hLowAbsorb := eventually_pintz2023_low_shell_endpoint_absorbed
    (eta := eta) hC₀.le hepsilon
  have hMiddleAbsorb := eventually_pintz2023_middle_shell_endpoint_absorbed
    hC₁.le heta hepsilon
  have hTail := eventually_pintz2023GramCutoff_tail_le (1 : ℝ)
  have hLog : ∀ᶠ A : ℕ in atTop, 1 ≤ Real.log A := by
    have hNatTop : Tendsto (fun A : ℕ => (A : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    exact (Real.tendsto_log_atTop.comp hNatTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hCutoffScale, hLowAbsorb, hMiddleAbsorb, hTail, hLog,
    eventually_ge_atTop 4] with A hCutoffScaleA hLowFinal hMiddleFinal
      hTailA hLogA hAFour
  intro xi t T hxiNonneg hreal hxi hden ht htT hT
    hcritical hSmallB
  have hA : 0 < A := by omega
  have hAOne : 1 ≤ A := by omega
  have hM : A ≤ pintz2023GramCutoff A := le_pintz2023GramCutoff hLogA
  have hScaleM : (pintz2023GramCutoff A : ℝ) ≤
      4 * t ^ (2 / (r : ℝ)) :=
    hCutoffScaleA t ht hSmallB
  have hScaleA : (A : ℝ) ≤ 4 * t ^ (2 / (r : ℝ)) := by
    have hMReal : (A : ℝ) ≤ (pintz2023GramCutoff A : ℝ) := by
      exact_mod_cast hM
    exact hMReal.trans hScaleM
  have hLowExact := hLow A xi eta t hA heta (zero_lt_one.trans_le ht)
    hxi hScaleA
  have hMiddleExact := hMiddle A (pintz2023GramCutoff A) xi eta t T
    hA hM heta hxi hden (zero_lt_one.trans_le ht) htT hT hcritical hScaleM
  have hAssembly := norm_pintz2023SmoothedZetaSum_le_source_dyadic
    (kernelScale := A) (A := A) (M := pintz2023GramCutoff A)
    (xi := xi + 4 * eta) (t := t) hA hAOne hM hreal
  have hLowEndpoint := pintz2023_low_raw_shell_sum_le_endpoint
    hr hC₀.le hepsilon hepsilonUpper hA heta hxiNonneg
      (zero_lt_one.trans_le ht) htT hT hden hcritical
  have hMiddleEndpoint := pintz2023_middle_gram_shell_sum_le
    (A := A) (M := pintz2023GramCutoff A)
    hC₁.le heta hepsilon hA
  have hLowBound :
      ‖pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta) 1 A t‖ ≤
        (A : ℝ) ^ (4 * eta - 2 * epsilon) :=
    hLowExact.trans (hLowEndpoint.trans hLowFinal)
  have hMiddleBound :
      (∑ j ∈ Finset.range (Nat.clog 2 (pintz2023GramCutoff A)),
        ‖pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta)
          (2 ^ j * A)
          (min (pintz2023GramCutoff A) (2 ^ (j + 1) * A)) t‖) ≤
        (A : ℝ) ^ (4 * eta - 2 * epsilon) :=
    hMiddleExact.trans (hMiddleEndpoint.trans hMiddleFinal)
  let s : ℂ := ((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ)
  have hs : 0 ≤ s.re := by dsimp only [s]; simpa using hreal
  have hOne : ‖pintz2023SmoothedZetaTerm A s 1‖ ≤ 1 := by
    have hterm := norm_pintz2023SmoothedZetaTerm_le_exp
      (N := A) (n := 1) (s := s) hA (by omega) hs
    exact hterm.trans (by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hTargetNonneg : 0 ≤ 4 * eta - 2 * epsilon := by linarith
  have hPowerOne : 1 ≤ (A : ℝ) ^ (4 * eta - 2 * epsilon) :=
    Real.one_le_rpow (by exact_mod_cast hAOne) hTargetNonneg
  have hTailBound :
      Real.exp (-((pintz2023GramCutoff A + 1 : ℕ) : ℝ) / (2 * A)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * A)))⁻¹ ≤
        (A : ℝ) ^ (4 * eta - 2 * epsilon) := by
    calc
      _ ≤ 4 * (A : ℝ) ^ (-(1 : ℝ)) := hTailA
      _ ≤ 1 := by
        rw [Real.rpow_neg_one]
        change (4 : ℝ) / (A : ℝ) ≤ 1
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (A : ℝ))]
        have hAFourReal : (4 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hAFour
        simpa using hAFourReal
      _ ≤ _ := hPowerOne
  have hOneFinal : ‖pintz2023SmoothedZetaTerm A s 1‖ ≤
      (A : ℝ) ^ (4 * eta - 2 * epsilon) := hOne.trans hPowerOne
  dsimp only [s] at hOneFinal
  exact hAssembly.trans (by nlinarith)

#print axioms eventually_pintz2023_smallB_complete_gram_native

end

end GafniTao
