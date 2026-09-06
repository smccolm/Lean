import GafniTao.Pintz2023Equation423

/-!
# Pintz (2023), equation (4.21) inside the smoothed Gram sum

Corollary 3 controls the unsmoothed block at
`xi = eta_nu + eta_kappa`.  Exact Abel transfers insert first `n^(4 eta)`
and then both exponentials of the Halasz kernel.  This file records the
result on every middle dyadic block, with all scale hypotheses visible.
-/

namespace GafniTao

noncomputable section

/-- The literal kernel-weighted middle-block form of (4.21). -/
theorem pintz2023_equation421_kernel_block_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N L R : ℕ) (xi eta t T : ℝ),
        0 < N → 0 < L → L < R → R ≤ 2 * L →
        0 ≤ eta →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
        0 < t → t ≤ T → 1 ≤ T →
        pintz2023CriticalScale r xi epsilon T ≤ (L : ℝ) →
        (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
          C * (R : ℝ) ^ (4 * eta) * (L : ℝ) ^ (-3 * epsilon) := by
  obtain ⟨C₀, hC₀, hCor⟩ :=
    pintz2023_corollary_three_native r epsilon B hr hepsilon hB
  refine ⟨4 * C₀, mul_pos (by norm_num) hC₀, ?_⟩
  intro N L R xi eta t T hN hL hLR hR heta hxi hden ht htT hT
    hcritical hscale
  have hPartial : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock xi L (L + j) t‖ ≤
        C₀ * (L : ℝ) ^ (-3 * epsilon) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      positivity
    · exact hCor xi L (L + j) t T hxi hden hL (by omega)
        (by omega) ht htT hT hcritical hscale
  have hBPartial : 0 ≤ C₀ * (L : ℝ) ^ (-3 * epsilon) := by positivity
  have hShifted : ∀ j, j ≤ R - L →
      ‖pintz2023WeightedBlock (xi + 4 * eta) L (L + j) t‖ ≤
        2 * (R : ℝ) ^ (4 * eta) *
          (C₀ * (L : ℝ) ^ (-3 * epsilon)) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [pintz2023WeightedBlock]
      positivity
    · have hLj : L < L + j := by omega
      have hLjR : L + j ≤ R := by omega
      have hShift := norm_pintz2023WeightedBlock_shift_le_of_prefix
        hL hLj (show 0 ≤ 4 * eta by positivity)
          (fun q hq => hPartial q (by omega))
      have hpow : (((L + j : ℕ) : ℝ)) ^ (4 * eta) ≤
          (R : ℝ) ^ (4 * eta) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _)
        · exact_mod_cast hLjR
        · positivity
      exact hShift.trans (by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by norm_num)) hBPartial)
  have hKernel :=
    norm_pintz2023HalaszKernelWeightedBlock_le_exp_of_prefix
      hN hLR hShifted
  have hExpOne :
      Real.exp (-((L + 1 : ℕ) : ℝ) / (2 * N)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hExpTwo :
      Real.exp (-((L + 1 : ℕ) : ℝ) / N) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hTailNonneg : 0 ≤ 2 * (R : ℝ) ^ (4 * eta) *
      (C₀ * (L : ℝ) ^ (-3 * epsilon)) := by positivity
  calc
    ‖pintz2023HalaszKernelWeightedBlock N (xi + 4 * eta) L R t‖ ≤
        (Real.exp (-((L + 1 : ℕ) : ℝ) / (2 * N)) +
          Real.exp (-((L + 1 : ℕ) : ℝ) / N)) *
            (2 * (R : ℝ) ^ (4 * eta) *
              (C₀ * (L : ℝ) ^ (-3 * epsilon))) := hKernel
    _ ≤ 2 * (2 * (R : ℝ) ^ (4 * eta) *
              (C₀ * (L : ℝ) ^ (-3 * epsilon))) := by
      gcongr
      linarith
    _ = (4 * C₀) * (R : ℝ) ^ (4 * eta) *
        (L : ℝ) ^ (-3 * epsilon) := by ring

#print axioms pintz2023_equation421_kernel_block_native

end

end GafniTao
