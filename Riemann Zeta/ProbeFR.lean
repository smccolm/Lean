import RiemannZeta.GuthMaynard.ClassicalEndpointSlab

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

#check ContDiff.continuous_deriv
#check ContDiff.continuous_iteratedDeriv
#check IsCompact.bddAbove_image
#check IsCompact.exists_isMaxOn
#check ContinuousOn.bddAbove_range
#check intervalIntegral.integral_mono_on
#check intervalIntegral.norm_integral_le_abs_integral_norm
#check intervalIntegral.integral_comp_mul_deriv
#check intervalIntegral.integral_comp_mul_left
#check ContDiff.differentiable
#check DifferentiableAt.hasDerivAt
#check HasDerivAt.clm_apply
#check HasDerivAt.ofReal_comp
#check HasDerivAt.norm
#check ContinuousOn.norm
#check IsCompact.isBoundedUnder_le

theorem weighted_sum_eq_endpoint_sub_differences
    (w : ℕ → ℂ) (a : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, w m * a m) =
      w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m) -
        ∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m) := by
  induction M with
  | zero => simp
  | succ M ih =>
      change (∑ m ∈ Finset.Icc 1 (M + 1), w m * a m) =
        w ((M + 1) + 1) * (∑ m ∈ Finset.Icc 1 (M + 1), a m) -
          ∑ j ∈ Finset.Icc 1 (M + 1),
            (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      rw [ih]
      ring

theorem sum_successive_differences (v : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (v (j + 1) - v j)) = v (M + 1) - v 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
      change (∑ j ∈ Finset.Icc 1 (M + 1), (v (j + 1) - v j)) =
        v ((M + 1) + 1) - v 1
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
      ring

theorem norm_weighted_sum_le_of_partial_sum
    (w : ℕ → ℂ) (a : ℕ → ℂ) (M : ℕ) (R W D : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 M,
      ‖∑ m ∈ Finset.Icc 1 j, a m‖ ≤ R)
    (hendpoint : ‖w (M + 1)‖ ≤ W)
    (hdifference : (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) ≤ D) :
    ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤ (W + D) * R := by
  have hpartialM : ‖∑ m ∈ Finset.Icc 1 M, a m‖ ≤ R := by
    by_cases hM : M = 0
    · subst M
      simpa using hR
    · exact hpartial M (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hW : 0 ≤ W := (norm_nonneg (w (M + 1))).trans hendpoint
  rw [weighted_sum_eq_endpoint_sub_differences]
  calc
    ‖w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m) -
        ∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ ≤
      ‖w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m)‖ +
        ‖∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ := norm_sub_le _ _
    _ ≤ W * R + ∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖ * R := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hendpoint hpartialM (norm_nonneg _) hW
      · calc
          ‖∑ j ∈ Finset.Icc 1 M,
              (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ ≤
              ∑ j ∈ Finset.Icc 1 M,
                ‖(w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖ * R := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpartial j hj) (norm_nonneg _)
    _ = W * R + (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) * R := by
      rw [Finset.sum_mul]
    _ ≤ W * R + D * R := by gcongr
    _ = (W + D) * R := by ring

theorem norm_typeIReflectedFixedPolynomial_le_two_mul_max_prefix
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (M : ℕ) (R : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 M,
      ‖∑ m ∈ Finset.Icc 1 j,
        (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ ≤ R) :
    ‖typeIReflectedFixedPolynomial sigma u M‖ ≤
      2 * (M + 1 : ℝ) ^ sigma * R := by
  let w : ℕ → ℂ := fun m => (((m : ℝ) ^ sigma : ℝ) : ℂ)
  let a : ℕ → ℂ := fun m => (m : ℂ) ^ (((u : ℂ) * Complex.I))
  have hdiffPoint : ∀ j : ℕ,
      ‖w (j + 1) - w j‖ = (j + 1 : ℝ) ^ sigma - (j : ℝ) ^ sigma := by
    intro j
    dsimp only [w]
    push_cast
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg j)
        (show (j : ℝ) ≤ (j : ℝ) + 1 by norm_num) hsigma)
  have hdiff : (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) ≤
      (M + 1 : ℝ) ^ sigma - 1 := by
    simp_rw [hdiffPoint]
    have htel := sum_successive_differences
      (fun n : ℕ => (n : ℝ) ^ sigma) M
    convert htel.le using 1 <;> norm_num
  have hend : ‖w (M + 1)‖ ≤ (M + 1 : ℝ) ^ sigma := by
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    norm_num
  have hbase := norm_weighted_sum_le_of_partial_sum w a M R
    ((M + 1 : ℝ) ^ sigma) ((M + 1 : ℝ) ^ sigma - 1)
    hR hpartial hend hdiff
  unfold typeIReflectedFixedPolynomial
  change ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤ _
  calc
    ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤
      ((M + 1 : ℝ) ^ sigma + ((M + 1 : ℝ) ^ sigma - 1)) * R := hbase
    _ ≤ 2 * (M + 1 : ℝ) ^ sigma * R := by
      have hRpow : 0 ≤ (M + 1 : ℝ) ^ sigma := Real.rpow_nonneg (by positivity) _
      nlinarith

theorem exists_large_reflected_prefix
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (M : ℕ) (R : ℝ)
    (hR : 0 ≤ R)
    (hLarge : 2 * (M + 1 : ℝ) ^ sigma * R <
      ‖typeIReflectedFixedPolynomial sigma u M‖) :
    ∃ j ∈ Finset.Icc 1 M, R <
      ‖∑ m ∈ Finset.Icc 1 j,
        (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hLarge)
    (norm_typeIReflectedFixedPolynomial_le_two_mul_max_prefix
      hsigma u M R hR h)

end RiemannZeta.GuthMaynard
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint
#check Nat.le_pow_clog
#check Nat.clog_pos
#check RiemannZeta.GuthMaynard.wideDirichletPoly
#check RiemannZeta.GuthMaynard.wideDirichletPoly_eq_sum_blocks
#check RiemannZeta.GuthMaynard.exists_dyadic_block_and_subset
