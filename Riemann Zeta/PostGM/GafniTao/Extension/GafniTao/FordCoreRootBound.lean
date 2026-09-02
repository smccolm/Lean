import GafniTao.FordScaledCoreCompact

/-!
# The quantitative root of Ford's Lemma 5.1 core

This file combines the exact source-core comparison with the negative exponent
obtained from the central degree band, and then takes the literal
`(2rs)⁻¹` power occurring in Lemma 5.1 at `r=s=2k²`.
-/

namespace GafniTao

noncomputable section

theorem fordScaledCoreCoefficient_nonneg (k : ℕ) :
    0 ≤ fordScaledCoreCoefficient k := by
  unfold fordScaledCoreCoefficient
  positivity

/-- The literal Lemma-5.1 source core has a power saving before taking its
`2rs`-th root. -/
theorem fordLemma51SourceCore_le_power_saving
    {k N : ℕ} {t : ℝ} (hk : 1000 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    fordLemma51SourceCore k 1 k
        (fordDoubleSquareDegree k) (fordDoubleSquareDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t ≤
      fordScaledCoreCoefficient k *
        (N : ℝ) ^ (-((k : ℝ) ^ 2 / 136400)) := by
  have hk1000 : 1000 ≤ k := hk
  have hsource := fordLemma51SourceCore_scaled_le hk hN ht hlower hupper
  have hmajor := fordScaledSourceCoreMajorant_le_decay hk hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hexponent := fordScaledCoreDecayExponent_le hk1000
  have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  exact hsource.trans (hmajor.trans
    (mul_le_mul_of_nonneg_left hpow (fordScaledCoreCoefficient_nonneg k)))

theorem ford_double_square_root_exponent
    {k : ℕ} (hk : 1 ≤ k) :
    (-((k : ℝ) ^ 2 / 136400)) *
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) =
      -(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2)) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Rooted form of the power saving.  The exponent `1091200` is exactly
`8 * 136400`, since `2rs=8k⁴` for the selected double-square moments. -/
theorem fordLemma51SourceCore_root_le
    {k N : ℕ} {t : ℝ} (hk : 1000 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    (fordLemma51SourceCore k 1 k
        (fordDoubleSquareDegree k) (fordDoubleSquareDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
      (fordScaledCoreCoefficient k) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
        (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
  have hk1000 : 1000 ≤ k := hk
  have hk1 : 1 ≤ k := by omega
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hsource0 : 0 ≤ fordLemma51SourceCore k 1 k
      (fordDoubleSquareDegree k) (fordDoubleSquareDegree k)
      ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
      (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t := by
    apply fordLemma51SourceCore_nonneg
    · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      exact Real.one_le_rpow hNreal (by norm_num)
    · positivity
    · unfold fordDoubleSquareDegree
      positivity
    · unfold fordDoubleSquareDegree
      positivity
    · positivity
    · exact ht
  have hq : 0 ≤ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := by positivity
  have hroot := Real.rpow_le_rpow hsource0
    (fordLemma51SourceCore_le_power_saving hk hN ht hlower hupper) hq
  have hcoeff0 := fordScaledCoreCoefficient_nonneg k
  calc
    _ ≤ (fordScaledCoreCoefficient k *
          (N : ℝ) ^ (-((k : ℝ) ^ 2 / 136400))) ^
            (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := hroot
    _ = (fordScaledCoreCoefficient k) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
        ((N : ℝ) ^ (-((k : ℝ) ^ 2 / 136400))) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := by
      rw [Real.mul_rpow hcoeff0 (Real.rpow_nonneg hN0 _)]
    _ = (fordScaledCoreCoefficient k) ^
          (1 / (((8 * k ^ 4 : ℕ) : ℝ))) *
        (N : ℝ) ^ (-(1 / ((1091200 : ℝ) * (k : ℝ) ^ 2))) := by
      rw [← Real.rpow_mul hN0, ford_double_square_root_exponent hk1]

#print axioms fordLemma51SourceCore_le_power_saving
#print axioms ford_double_square_root_exponent
#print axioms fordLemma51SourceCore_root_le

end

end GafniTao
