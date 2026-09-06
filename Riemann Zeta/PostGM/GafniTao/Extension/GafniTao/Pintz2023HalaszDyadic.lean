import GafniTao.Pintz2023Equation421
import GafniTao.Pintz2023SmoothedZeta

/-!
# Exact dyadic decomposition of Pintz's smoothed Gram series

The terminal shell is cut at the literal natural endpoint.  This module is
pure bookkeeping: it neither enlarges a block nor discards the `n = 1`
endpoint.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem pintz2023HalaszKernelWeightedBlock_add
    (N : ℕ) (xi t : ℝ) {A B C : ℕ} (hAB : A ≤ B) (hBC : B ≤ C) :
    pintz2023HalaszKernelWeightedBlock N xi A B t +
        pintz2023HalaszKernelWeightedBlock N xi B C t =
      pintz2023HalaszKernelWeightedBlock N xi A C t := by
  unfold pintz2023HalaszKernelWeightedBlock
  rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [Finset.Ioc_union_Ioc_eq_Ioc hAB hBC]

noncomputable def pintz2023HalaszDyadicShellSum
    (N : ℕ) (xi : ℝ) (r M : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range r,
    pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
      (min M (2 ^ (j + 1))) t

/-- The first `r` shells are exactly the block `(1,min(M,2^r)]`. -/
theorem pintz2023HalaszDyadicShellSum_eq_block
    (N : ℕ) (xi : ℝ) (r M : ℕ) (t : ℝ) :
    pintz2023HalaszDyadicShellSum N xi r M t =
      pintz2023HalaszKernelWeightedBlock N xi 1 (min M (2 ^ r)) t := by
  induction r with
  | zero =>
      simp [pintz2023HalaszDyadicShellSum,
        pintz2023HalaszKernelWeightedBlock]
  | succ r ih =>
      rw [pintz2023HalaszDyadicShellSum, Finset.sum_range_succ]
      change pintz2023HalaszDyadicShellSum N xi r M t +
          pintz2023HalaszKernelWeightedBlock N xi (2 ^ r)
            (min M (2 ^ (r + 1))) t = _
      rw [ih]
      by_cases hM : M ≤ 2 ^ r
      · have hMin : min M (2 ^ r) = M := min_eq_left hM
        have hPow : 2 ^ r ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hMinSucc : min M (2 ^ (r + 1)) = M :=
          min_eq_left (hM.trans hPow)
        rw [hMin, hMinSucc]
        unfold pintz2023HalaszKernelWeightedBlock
        rw [Finset.Ioc_eq_empty_of_le hM, Finset.sum_empty, add_zero]
      · have hPowM : 2 ^ r ≤ M := by omega
        have hPowSucc : 2 ^ r ≤ 2 ^ (r + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hMiddle : 2 ^ r ≤ min M (2 ^ (r + 1)) :=
          le_min hPowM hPowSucc
        rw [min_eq_right hPowM]
        exact pintz2023HalaszKernelWeightedBlock_add N xi t
          (one_le_pow₀ (by omega : (1 : ℕ) ≤ 2)) hMiddle

theorem pintz2023HalaszDyadicShellSum_eq_full_block
    (N : ℕ) (xi : ℝ) {r M : ℕ} (t : ℝ) (hM : M ≤ 2 ^ r) :
    pintz2023HalaszDyadicShellSum N xi r M t =
      pintz2023HalaszKernelWeightedBlock N xi 1 M t := by
  rw [pintz2023HalaszDyadicShellSum_eq_block, min_eq_left hM]

/-- The finite smoothed series is its exact first term plus its dyadic
shells. -/
theorem sum_Icc_pintz2023SmoothedZetaTerm_eq_one_add_dyadic
    {N M : ℕ} {xi t : ℝ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M,
        pintz2023SmoothedZetaTerm N
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) n) =
      pintz2023SmoothedZetaTerm N
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) 1 +
        pintz2023HalaszDyadicShellSum N xi (Nat.clog 2 M) M t := by
  have hCover : M ≤ 2 ^ Nat.clog 2 M := Nat.le_pow_clog (by omega) M
  rw [Finset.Icc_eq_cons_Ioc hM, Finset.sum_cons]
  rw [pintz2023HalaszDyadicShellSum_eq_full_block N xi t hCover]
  congr 1
  unfold pintz2023HalaszKernelWeightedBlock
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  rw [pintz2023SmoothedZetaTerm_eq hnPos]
  rw [Complex.real_smul, Complex.real_smul]
  have hpow :
      (n : ℂ) ^ (-(((1 - xi : ℝ) : ℂ) + I * (t : ℂ))) =
        (((n : ℝ) ^ (-(1 - xi)) : ℝ) : ℂ) *
          (n : ℂ) ^ (-(t : ℂ) * I) := by
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
    rw [show -(((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) =
        -((1 - xi : ℝ) : ℂ) + (-(t : ℂ) * I) by ring]
    rw [Complex.cpow_add _ _ hnC]
    congr 1
    rw [show -((1 - xi : ℝ) : ℂ) = ((-(1 - xi) : ℝ) : ℂ) by
      push_cast
      ring]
    exact (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ n)
      (-(1 - xi))).symm
  rw [hpow]

#print axioms pintz2023HalaszKernelWeightedBlock_add
#print axioms pintz2023HalaszDyadicShellSum_eq_block
#print axioms sum_Icc_pintz2023SmoothedZetaTerm_eq_one_add_dyadic

end

end GafniTao
