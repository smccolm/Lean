import GafniTao.Pintz2023HalaszAssembly

/-!
# Pintz (2023), source-aligned dyadic split of the Gram series

The powered polynomial begins at `A_h`.  Pintz applies (4.23) on `(1,A_h]`
and (4.21) on `(A_h,B_h log^2 B_h]`.  Relative dyadic shells beginning
exactly at `A_h` avoid an artificial shell crossing that boundary.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023HalaszRelativeDyadicShellSum
    (kernelScale : ℕ) (xi : ℝ) (A r M : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range r,
    pintz2023HalaszKernelWeightedBlock kernelScale xi (2 ^ j * A)
      (min M (2 ^ (j + 1) * A)) t

/-- The first `r` relative shells are exactly
`(A,min(M,2^r A)]`. -/
theorem pintz2023HalaszRelativeDyadicShellSum_eq_block
    (kernelScale : ℕ) (xi : ℝ) (A r M : ℕ) (t : ℝ) :
    pintz2023HalaszRelativeDyadicShellSum kernelScale xi A r M t =
      pintz2023HalaszKernelWeightedBlock kernelScale xi A
        (min M (2 ^ r * A)) t := by
  induction r with
  | zero =>
      simp [pintz2023HalaszRelativeDyadicShellSum,
        pintz2023HalaszKernelWeightedBlock]
  | succ r ih =>
      rw [pintz2023HalaszRelativeDyadicShellSum, Finset.sum_range_succ]
      change pintz2023HalaszRelativeDyadicShellSum kernelScale xi A r M t +
          pintz2023HalaszKernelWeightedBlock kernelScale xi (2 ^ r * A)
            (min M (2 ^ (r + 1) * A)) t = _
      rw [ih]
      by_cases hM : M ≤ 2 ^ r * A
      · have hPow : 2 ^ r * A ≤ 2 ^ (r + 1) * A := by
          exact Nat.mul_le_mul_right A
            (Nat.pow_le_pow_right (by omega) (by omega))
        rw [min_eq_left hM, min_eq_left (hM.trans hPow)]
        unfold pintz2023HalaszKernelWeightedBlock
        rw [Finset.Ioc_eq_empty_of_le hM, Finset.sum_empty, add_zero]
      · have hAM : 2 ^ r * A ≤ M := by omega
        have hPow : 2 ^ r * A ≤ 2 ^ (r + 1) * A := by
          exact Nat.mul_le_mul_right A
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hMiddle : 2 ^ r * A ≤ min M (2 ^ (r + 1) * A) :=
          le_min hAM hPow
        rw [min_eq_right hAM]
        exact pintz2023HalaszKernelWeightedBlock_add kernelScale xi t
          (by exact Nat.le_mul_of_pos_left A (pow_pos (by omega) r)) hMiddle

/-- With `A >= 1`, `clog 2 M` relative shells cover every integer through
`M`. -/
theorem pintz2023HalaszRelativeDyadicShellSum_eq_full_block
    (kernelScale : ℕ) (xi : ℝ) {A M : ℕ} (t : ℝ)
    (hA : 1 ≤ A) :
    pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
        (Nat.clog 2 M) M t =
      pintz2023HalaszKernelWeightedBlock kernelScale xi A M t := by
  rw [pintz2023HalaszRelativeDyadicShellSum_eq_block]
  rw [min_eq_left]
  calc
    M ≤ 2 ^ Nat.clog 2 M := Nat.le_pow_clog (by omega) M
    _ = 2 ^ Nat.clog 2 M * 1 := by omega
    _ ≤ 2 ^ Nat.clog 2 M * A :=
      Nat.mul_le_mul_left (2 ^ Nat.clog 2 M) hA

/-- Exact finite source split at the powered polynomial endpoint `A_h`. -/
theorem sum_Icc_pintz2023SmoothedZetaTerm_eq_source_dyadic
    {kernelScale A M : ℕ} {xi t : ℝ}
    (hA : 1 ≤ A) (hAM : A ≤ M) :
    (∑ n ∈ Finset.Icc 1 M,
        pintz2023SmoothedZetaTerm kernelScale
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) n) =
      pintz2023SmoothedZetaTerm kernelScale
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) 1 +
        pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t +
        pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
          (Nat.clog 2 M) M t := by
  have hM : 1 ≤ M := hA.trans hAM
  rw [sum_Icc_pintz2023SmoothedZetaTerm_eq_one_add_dyadic hM]
  rw [pintz2023HalaszDyadicShellSum_eq_full_block kernelScale xi t
    (Nat.le_pow_clog (by omega) M)]
  rw [pintz2023HalaszRelativeDyadicShellSum_eq_full_block
    kernelScale xi t hA]
  rw [show pintz2023HalaszKernelWeightedBlock kernelScale xi 1 M t =
      pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t +
        pintz2023HalaszKernelWeightedBlock kernelScale xi A M t from
    (pintz2023HalaszKernelWeightedBlock_add kernelScale xi t hA hAM).symm]
  ring

/-- Norm bound for the exact relative shell sum. -/
theorem norm_pintz2023HalaszRelativeDyadicShellSum_le
    (kernelScale : ℕ) (xi : ℝ) (A r M : ℕ) (t : ℝ) :
    ‖pintz2023HalaszRelativeDyadicShellSum kernelScale xi A r M t‖ ≤
      ∑ j ∈ Finset.range r,
        ‖pintz2023HalaszKernelWeightedBlock kernelScale xi (2 ^ j * A)
          (min M (2 ^ (j + 1) * A)) t‖ := by
  unfold pintz2023HalaszRelativeDyadicShellSum
  exact norm_sum_le _ _

/-- Complete infinite-series assembly at Pintz's source boundary `A_h`. -/
theorem norm_pintz2023SmoothedZetaSum_le_source_dyadic
    {kernelScale A M : ℕ} {xi t : ℝ}
    (hkernel : 0 < kernelScale) (hA : 1 ≤ A) (hAM : A ≤ M)
    (hreal : 0 ≤ 1 - xi) :
    ‖pintz2023SmoothedZetaSum kernelScale
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
      ‖pintz2023SmoothedZetaTerm kernelScale
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) 1‖ +
        ‖pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t‖ +
        (∑ j ∈ Finset.range (Nat.clog 2 M),
          ‖pintz2023HalaszKernelWeightedBlock kernelScale xi (2 ^ j * A)
            (min M (2 ^ (j + 1) * A)) t‖) +
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * kernelScale)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * kernelScale)))⁻¹ := by
  let s : ℂ := ((1 - xi : ℝ) : ℂ) + I * (t : ℂ)
  let F : ℂ := ∑ n ∈ Finset.Icc 1 M,
    pintz2023SmoothedZetaTerm kernelScale s n
  have hs : 0 ≤ s.re := by dsimp only [s]; simpa using hreal
  have htailF :
      ‖pintz2023SmoothedZetaSum kernelScale s - F‖ ≤
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * kernelScale)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * kernelScale)))⁻¹ := by
    simpa only [F] using
      (norm_pintz2023SmoothedZetaSum_sub_sum_Icc_le
        (N := kernelScale) (M := M) (s := s) hkernel hs)
  have hfinite : F =
      pintz2023SmoothedZetaTerm kernelScale s 1 +
        pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t +
        pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
          (Nat.clog 2 M) M t := by
    dsimp only [F, s]
    exact sum_Icc_pintz2023SmoothedZetaTerm_eq_source_dyadic hA hAM
  have hnormF : ‖F‖ ≤
      ‖pintz2023SmoothedZetaTerm kernelScale s 1‖ +
        ‖pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t‖ +
        ‖pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
          (Nat.clog 2 M) M t‖ := by
    rw [hfinite]
    calc
      ‖pintz2023SmoothedZetaTerm kernelScale s 1 +
          pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t +
          pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
            (Nat.clog 2 M) M t‖ ≤
        ‖pintz2023SmoothedZetaTerm kernelScale s 1 +
          pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t‖ +
          ‖pintz2023HalaszRelativeDyadicShellSum kernelScale xi A
            (Nat.clog 2 M) M t‖ := norm_add_le _ _
      _ ≤ _ := by
        linarith [norm_add_le
          (pintz2023SmoothedZetaTerm kernelScale s 1)
          (pintz2023HalaszKernelWeightedBlock kernelScale xi 1 A t)]
  have hshell := norm_pintz2023HalaszRelativeDyadicShellSum_le
    kernelScale xi A (Nat.clog 2 M) M t
  have hsplit : pintz2023SmoothedZetaSum kernelScale s =
      (pintz2023SmoothedZetaSum kernelScale s - F) + F := by ring
  calc
    ‖pintz2023SmoothedZetaSum kernelScale s‖ ≤
        ‖pintz2023SmoothedZetaSum kernelScale s - F‖ + ‖F‖ := by
      calc
        _ = ‖(pintz2023SmoothedZetaSum kernelScale s - F) + F‖ :=
          congrArg norm hsplit
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by
      have := add_le_add htailF hnormF
      dsimp only [s] at this ⊢
      nlinarith [hshell]

#print axioms pintz2023HalaszRelativeDyadicShellSum_eq_block
#print axioms pintz2023HalaszRelativeDyadicShellSum_eq_full_block
#print axioms sum_Icc_pintz2023SmoothedZetaTerm_eq_source_dyadic
#print axioms norm_pintz2023SmoothedZetaSum_le_source_dyadic

end

end GafniTao
