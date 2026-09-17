import Tao2026.VinogradovIKFinite

/-!
# Unconditional Vinogradov estimate

This module assembles the effective-degree coefficient estimate, local
product sums, interval pair sums, and the effective Taylor transfer.  It
closes `VinogradovExponentialSumEstimate` with an explicit absolute constant.
-/

namespace Tao2026

open scoped ContDiff

/-- Pointwise Taylor-polynomial product sum at the effective degree. -/
theorem source_vinogradovIKTaylorPolynomialLocalProductSum_bound
    {X F α : ℝ} {n : ℕ} {f : ℝ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hderiv : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          (n : ℝ) ^ r / (r.factorial : ℝ) * |iteratedDeriv r f n| ∧
        (n : ℝ) ^ r / (r.factorial : ℝ) * |iteratedDeriv r f n| ≤
          α ^ (r ^ 3) * F) :
    ‖vinogradovTaylorPolynomialLocalProductSum f
        (vinogradovIKDegree X F) n (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (vinogradovIKBilinearConstant * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
  rw [norm_vinogradovTaylorPolynomialLocalProductSum_eq_bilinearSum,
    vinogradovTaylorBilinearSum_eq_bilinearPolynomialSum]
  apply source_bilinear_IK_uniform_bound hX hFhigh hα hn
  intro r hr hrK
  rw [pow_mul_abs_vinogradovTaylorCoefficient]
  apply hderiv r hr
  have htop :=
    vinogradovIKDegree_add_one_le_vinogradovDerivativeCutoff hX hFhigh
  omega

/-- Interval pair-sum estimate at the effective degree. -/
theorem source_vinogradovIKTaylorPolynomialPairSum_bound
    {X F α : ℝ} {a b : ℕ} {f : ℝ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hI : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X))
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        ((vinogradovIKBilinearConstant + 9) * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
  let V := vinogradovAveragingRange X
  let K := vinogradovIKDegree X F
  let E := Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  have hpoint : ∀ n ∈ Finset.Ico a (b - V ^ 2),
      ‖vinogradovTaylorPolynomialLocalProductSum f K n V‖ ≤
        ((V ^ 2 : ℕ) : ℝ) * (vinogradovIKBilinearConstant * α * E) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnab : (n : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      constructor
      · exact_mod_cast hn'.1
      · exact_mod_cast (show n ≤ b by omega)
    simpa only [K, V, E] using
      source_vinogradovIKTaylorPolynomialLocalProductSum_bound
        hX hFhigh hα (hI hnab)
        (fun r hr hrCutoff => hderiv n hnab r hr hrCutoff)
  have hpair := norm_vinogradovTaylorPolynomialPairSum_le_of_local
    f K a b V hpoint
  have hcardNat : (Finset.Ico a (b - V ^ 2)).card ≤ b - a := by
    simp only [Nat.card_Ico]
    omega
  have hcard : ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤ X := by
    have hcardBA : ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤
        ((b - a : ℕ) : ℝ) := by exact_mod_cast hcardNat
    by_cases hab : a < b
    · have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
      have hXa : X ≤ (a : ℝ) := (hI ⟨le_rfl, habReal⟩).1
      have hbX : (b : ℝ) ≤ 2 * X := (hI ⟨habReal, le_rfl⟩).2
      calc
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) := hcardBA
        _ = (b : ℝ) - (a : ℝ) := by rw [Nat.cast_sub hab.le]
        _ ≤ X := by linarith
    · have hzero : b - a = 0 := by omega
      rw [hzero, Nat.cast_zero] at hcardBA
      exact hcardBA.trans (by linarith)
  let B := α * X * E
  have hTaylor : Real.sqrt X + 2 * Real.pi ≤ 9 * B := by
    simpa only [B, E] using sqrt_add_two_pi_le_nine_mul_vinogradovScale
      hX hFhigh hα
  have hVtwo : ((V ^ 2 : ℕ) : ℝ) ≤ 9 * B := by
    calc
      ((V ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X := by
        simpa only [V] using vinogradovAveragingRange_sq_le_sqrt X
      _ ≤ Real.sqrt X + 2 * Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ 9 * B := hTaylor
  have hVnonneg : 0 ≤ ((V ^ 2 : ℕ) : ℝ) := by positivity
  have hlocalScale : 0 ≤ ((V ^ 2 : ℕ) : ℝ) *
      (vinogradovIKBilinearConstant * α * E) := by
    have hC := one_le_vinogradovIKBilinearConstant
    positivity
  calc
    ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b (vinogradovAveragingRange X)‖ =
      ‖vinogradovTaylorPolynomialPairSum f K a b V‖ := by rfl
    _ ≤ ((V ^ 2 : ℕ) : ℝ) * ((V ^ 2 : ℕ) : ℝ) +
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) *
          (((V ^ 2 : ℕ) : ℝ) *
            (vinogradovIKBilinearConstant * α * E)) := hpair
    _ ≤ ((V ^ 2 : ℕ) : ℝ) * (9 * B) +
        X * (((V ^ 2 : ℕ) : ℝ) *
          (vinogradovIKBilinearConstant * α * E)) :=
      add_le_add (mul_le_mul_of_nonneg_left hVtwo hVnonneg)
        (mul_le_mul_of_nonneg_right hcard hlocalScale)
    _ = ((V ^ 2 : ℕ) : ℝ) *
        ((vinogradovIKBilinearConstant + 9) * B) := by
      dsimp only [B]
      ring
    _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        ((vinogradovIKBilinearConstant + 9) * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
      dsimp only [V, B, E]
      ring

/-- Explicit unconditional witness for the exact Vinogradov exponential-sum
contract. -/
theorem vinogradovExponentialSumEstimateAt_IK :
    VinogradovExponentialSumEstimateAt
      ((vinogradovIKBilinearConstant + 9) + 9) := by
  refine ⟨by
    have := one_le_vinogradovIKBilinearConstant
    linarith, ?_⟩
  intro X F α a b f hX hFhigh hα hsmall hI hsmooth hderiv
  let B := α * X * Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  have hpoly := source_vinogradovIKTaylorPolynomialPairSum_bound
    hX hFhigh hα hI hderiv
  have hsum :=
    norm_sum_Ico_standardAdditiveCharacter_le_of_IKSourcePairSum_of_subset
      hX hFhigh hα hsmall hI hsmooth hderiv
      (A := (vinogradovIKBilinearConstant + 9) * B)
      (by simpa only [B, mul_assoc] using hpoly)
  have hTaylor : Real.sqrt X + 2 * Real.pi ≤ 9 * B := by
    simpa only [B] using sqrt_add_two_pi_le_nine_mul_vinogradovScale
      hX hFhigh hα
  calc
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
        Real.sqrt X + 2 * Real.pi +
          (vinogradovIKBilinearConstant + 9) * B := hsum
    _ ≤ 9 * B + (vinogradovIKBilinearConstant + 9) * B :=
      add_le_add hTaylor le_rfl
    _ = ((vinogradovIKBilinearConstant + 9) + 9) * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) := by
      dsimp only [B]
      ring

/-- The formerly residual source estimate is now unconditional. -/
theorem vinogradovExponentialSumEstimate_unconditional :
    VinogradovExponentialSumEstimate :=
  ⟨(vinogradovIKBilinearConstant + 9) + 9,
    vinogradovExponentialSumEstimateAt_IK⟩

end Tao2026
