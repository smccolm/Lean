import GafniTao.Pintz2023HalaszTail

/-!
# Pintz (2023), assembly of the complete smoothed Gram entry

The infinite series in (4.19) is split at a literal natural endpoint.  The
finite part is then decomposed into the exact `n = 1` term and terminal
dyadic shells.  The first omitted integer and the complete geometric tail
remain visible.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The norm of the exact dyadic shell sum is bounded by the sum of the
norms of its literal (possibly terminal) shells. -/
theorem norm_pintz2023HalaszDyadicShellSum_le
    (N : ℕ) (xi : ℝ) (r M : ℕ) (t : ℝ) :
    ‖pintz2023HalaszDyadicShellSum N xi r M t‖ ≤
      ∑ j ∈ Finset.range r,
        ‖pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
          (min M (2 ^ (j + 1))) t‖ := by
  unfold pintz2023HalaszDyadicShellSum
  exact norm_sum_le _ _

/-- Exact finite-cutoff assembly of the infinite smoothed series.  This is
the bookkeeping needed before applying (4.21) and (4.23) shell by shell. -/
theorem norm_pintz2023SmoothedZetaSum_le_one_shells_tail
    {N M : ℕ} {xi t : ℝ} (hN : 0 < N) (hM : 1 ≤ M)
    (hreal : 0 ≤ 1 - xi) :
    ‖pintz2023SmoothedZetaSum N
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
      ‖pintz2023SmoothedZetaTerm N
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) 1‖ +
        (∑ j ∈ Finset.range (Nat.clog 2 M),
          ‖pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
            (min M (2 ^ (j + 1))) t‖) +
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ := by
  let s : ℂ := ((1 - xi : ℝ) : ℂ) + I * (t : ℂ)
  let F : ℂ := ∑ n ∈ Finset.Icc 1 M, pintz2023SmoothedZetaTerm N s n
  have hs : 0 ≤ s.re := by
    dsimp only [s]
    simpa using hreal
  have htail := norm_pintz2023SmoothedZetaSum_sub_sum_Icc_le
    (N := N) (M := M) (s := s) hN hs
  have htailF :
      ‖pintz2023SmoothedZetaSum N s - F‖ ≤
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ := by
    simpa only [F] using htail
  have hfinite :
      F = pintz2023SmoothedZetaTerm N s 1 +
        pintz2023HalaszDyadicShellSum N xi (Nat.clog 2 M) M t := by
    dsimp only [F, s]
    exact sum_Icc_pintz2023SmoothedZetaTerm_eq_one_add_dyadic hM
  have hsplit :
      pintz2023SmoothedZetaSum N s =
        (pintz2023SmoothedZetaSum N s - F) + F := by ring
  have hnormF :
      ‖F‖ ≤ ‖pintz2023SmoothedZetaTerm N s 1‖ +
        ‖pintz2023HalaszDyadicShellSum N xi
          (Nat.clog 2 M) M t‖ := by
    rw [hfinite]
    exact norm_add_le _ _
  calc
    ‖pintz2023SmoothedZetaSum N s‖ ≤
        ‖pintz2023SmoothedZetaSum N s - F‖ + ‖F‖ := by
      calc
        _ = ‖(pintz2023SmoothedZetaSum N s - F) + F‖ :=
          congrArg norm hsplit
        _ ≤ _ := norm_add_le _ _
    _ ≤
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
            (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ +
          (‖pintz2023SmoothedZetaTerm N s 1‖ +
            ‖pintz2023HalaszDyadicShellSum N xi
              (Nat.clog 2 M) M t‖) := by
      exact add_le_add htailF hnormF
    _ ≤
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
            (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ +
          (‖pintz2023SmoothedZetaTerm N s 1‖ +
            ∑ j ∈ Finset.range (Nat.clog 2 M),
              ‖pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
                (min M (2 ^ (j + 1))) t‖) := by
      gcongr
      exact norm_pintz2023HalaszDyadicShellSum_le
        N xi (Nat.clog 2 M) M t
    _ = _ := by
      dsimp only [s]
      ring

/-- A shellwise majorant can be inserted into the preceding exact
assembly without changing the terminal-shell convention. -/
theorem norm_pintz2023SmoothedZetaSum_le_of_shell_majorants
    {N M : ℕ} {xi t : ℝ} (hN : 0 < N) (hM : 1 ≤ M)
    (hreal : 0 ≤ 1 - xi) (B : ℕ → ℝ)
    (hB : ∀ j, j < Nat.clog 2 M →
      ‖pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
          (min M (2 ^ (j + 1))) t‖ ≤ B j) :
    ‖pintz2023SmoothedZetaSum N
        (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
      ‖pintz2023SmoothedZetaTerm N
          (((1 - xi : ℝ) : ℂ) + I * (t : ℂ)) 1‖ +
        (∑ j ∈ Finset.range (Nat.clog 2 M), B j) +
        Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
          (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ := by
  have hshell :
      (∑ j ∈ Finset.range (Nat.clog 2 M),
          ‖pintz2023HalaszKernelWeightedBlock N xi (2 ^ j)
            (min M (2 ^ (j + 1))) t‖) ≤
        ∑ j ∈ Finset.range (Nat.clog 2 M), B j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hB j (Finset.mem_range.mp hj)
  refine (norm_pintz2023SmoothedZetaSum_le_one_shells_tail
    hN hM hreal).trans ?_
  gcongr

#print axioms norm_pintz2023HalaszDyadicShellSum_le
#print axioms norm_pintz2023SmoothedZetaSum_le_one_shells_tail
#print axioms norm_pintz2023SmoothedZetaSum_le_of_shell_majorants

end

end GafniTao
