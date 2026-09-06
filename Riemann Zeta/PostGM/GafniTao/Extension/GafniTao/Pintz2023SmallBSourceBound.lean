import GafniTao.Pintz2023HalaszSourceDyadic

/-!
# Pintz (2023), equations (4.21)--(4.23) at the powered source scale

Here `A` is the left endpoint of the powered Dirichlet polynomial and also
the Halasz smoothing scale.  The low shells end exactly at `A`; the relative
middle shells begin exactly there.  Thus no shell crosses the source split.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def pintz2023LowGramShellMajorant
    (C t eta epsilon : ℝ) (r A j : ℕ) : ℝ :=
  let L : ℕ := 2 ^ j
  let R : ℕ := min A (2 ^ (j + 1))
  C * ((L : ℝ) / A) * (R : ℝ) ^ (4 * eta) *
    (L : ℝ) ^ (-3 * epsilon) *
      (1 + t ^ pintz2023HBAlpha r /
        (L : ℝ) ^ (1 / (r : ℝ)))

noncomputable def pintz2023MiddleGramShellMajorant
    (C eta epsilon : ℝ) (A M j : ℕ) : ℝ :=
  let L : ℕ := 2 ^ j * A
  let R : ℕ := min M (2 ^ (j + 1) * A)
  if L < M then
    C * (R : ℝ) ^ (4 * eta) * (L : ℝ) ^ (-3 * epsilon)
  else 0

/-- The literal low block `(1,A]` is bounded by the sum of its (4.23)
majorants. -/
theorem pintz2023_low_block_equation423_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ) (xi eta t : ℝ),
        0 < A → 0 ≤ eta → 0 < t →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        (A : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta) 1 A t‖ ≤
          ∑ j ∈ Finset.range (Nat.clog 2 A),
            pintz2023LowGramShellMajorant C t eta epsilon r A j := by
  obtain ⟨C, hC, h423⟩ := pintz2023_equation423_shift_four_eta_native
    r epsilon B hr hepsilon hB
  refine ⟨C, hC, ?_⟩
  intro A xi eta t hA heta ht hxi hscale
  rw [← pintz2023HalaszDyadicShellSum_eq_full_block A (xi + 4 * eta) t
    (Nat.le_pow_clog (by omega) A)]
  refine (norm_pintz2023HalaszDyadicShellSum_le
    A (xi + 4 * eta) (Nat.clog 2 A) A t).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hjlt : j < Nat.clog 2 A := Finset.mem_range.mp hj
  let L : ℕ := 2 ^ j
  let R : ℕ := min A (2 ^ (j + 1))
  have hLA : L < A := Nat.pow_lt_of_lt_clog hjlt
  have hL : 0 < L := by dsimp only [L]; positivity
  have hLR : L < R := by
    dsimp only [R]
    apply lt_min hLA
    dsimp only [L]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hRtwo : R ≤ 2 * L := by
    dsimp only [R, L]
    calc
      min A (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
      _ = 2 * 2 ^ j := by rw [pow_succ, mul_comm]
  have hRA : R ≤ A := by dsimp only [R]; exact min_le_left _ _
  have hLscale : (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) := by
    have hLAReal : (L : ℝ) ≤ A := by exact_mod_cast hLA.le
    exact hLAReal.trans hscale
  have h := h423 A L R xi eta t hA hL hLR hRtwo hRA heta ht
    hxi hLscale
  simpa only [pintz2023LowGramShellMajorant, L, R] using h

/-- The literal middle block `(A,M]` is bounded shellwise by (4.21).
Empty terminal entries contribute exactly zero. -/
theorem pintz2023_middle_block_equation421_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A M : ℕ) (xi eta t T : ℝ),
        0 < A → A ≤ M → 0 ≤ eta →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
        0 < t → t ≤ T → 1 ≤ T →
        pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ) →
        (M : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        (∑ j ∈ Finset.range (Nat.clog 2 M),
          ‖pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta)
            (2 ^ j * A) (min M (2 ^ (j + 1) * A)) t‖) ≤
          ∑ j ∈ Finset.range (Nat.clog 2 M),
            pintz2023MiddleGramShellMajorant C eta epsilon A M j := by
  obtain ⟨C, hC, h421⟩ := pintz2023_equation421_kernel_block_native
    r epsilon B hr hepsilon hB
  refine ⟨C, hC, ?_⟩
  intro A M xi eta t T hA hAM heta hxi hden ht htT hT hcritical hscale
  apply Finset.sum_le_sum
  intro j hj
  let L : ℕ := 2 ^ j * A
  let R : ℕ := min M (2 ^ (j + 1) * A)
  by_cases hLM : L < M
  · have hL : 0 < L := Nat.mul_pos (pow_pos (by omega) _) hA
    have hLR : L < R := by
      dsimp only [R]
      apply lt_min hLM
      dsimp only [L]
      exact Nat.mul_lt_mul_of_pos_right
        (Nat.pow_lt_pow_right (by omega) (by omega)) hA
    have hRtwo : R ≤ 2 * L := by
      dsimp only [R, L]
      calc
        min M (2 ^ (j + 1) * A) ≤ 2 ^ (j + 1) * A := min_le_right _ _
        _ = 2 * (2 ^ j * A) := by rw [pow_succ]; ring
    have hcriticalL : pintz2023CriticalScale r xi epsilon T ≤ (L : ℝ) := by
      have hAL : A ≤ L := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right A (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))
      exact hcritical.trans (by exact_mod_cast hAL)
    have hLscale : (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) := by
      have hLMReal : (L : ℝ) ≤ M := by exact_mod_cast hLM.le
      exact hLMReal.trans hscale
    have h := h421 A L R xi eta t T hA hL hLR hRtwo heta hxi hden
      ht htT hT hcriticalL hLscale
    simpa only [pintz2023MiddleGramShellMajorant, L, R, if_pos hLM] using h
  · have hML : M ≤ L := Nat.le_of_not_gt hLM
    have hblock :
        pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta) L R t = 0 := by
      unfold pintz2023HalaszKernelWeightedBlock
      rw [Finset.Ioc_eq_empty_of_le]
      · simp
      · exact (min_le_left M _).trans hML
    rw [hblock, norm_zero]
    simp only [pintz2023MiddleGramShellMajorant, L, if_neg hLM]
    exact le_rfl

/-- Source-faithful complete small-`B_h` bound before the final elementary
power/logarithm absorption. -/
theorem pintz2023_smallB_source_gram_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (A M : ℕ) (xi eta t T : ℝ),
        0 < A → A ≤ M → 0 ≤ eta →
        0 ≤ 1 - (xi + 4 * eta) →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
        0 < t → t ≤ T → 1 ≤ T →
        pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ) →
        (M : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023SmoothedZetaSum A
            (((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          ‖pintz2023SmoothedZetaTerm A
              (((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ)) 1‖ +
            (∑ j ∈ Finset.range (Nat.clog 2 A),
              pintz2023LowGramShellMajorant C₀ t eta epsilon r A j) +
            (∑ j ∈ Finset.range (Nat.clog 2 M),
              pintz2023MiddleGramShellMajorant C₁ eta epsilon A M j) +
            Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * A)) *
              (1 - Real.exp (-(1 : ℝ) / (2 * A)))⁻¹ := by
  obtain ⟨C₀, hC₀, hlow⟩ :=
    pintz2023_low_block_equation423_native r epsilon B hr hepsilon hB
  obtain ⟨C₁, hC₁, hmiddle⟩ :=
    pintz2023_middle_block_equation421_native r epsilon B hr hepsilon hB
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro A M xi eta t T hA hAM heta hreal hxi hden ht htT hT
    hcritical hscale
  have hAssembly := norm_pintz2023SmoothedZetaSum_le_source_dyadic
    (t := t) hA hA hAM hreal
  have hLow := hlow A xi eta t hA heta ht hxi
    (by
      have hAMReal : (A : ℝ) ≤ M := by exact_mod_cast hAM
      exact hAMReal.trans hscale)
  have hMiddle := hmiddle A M xi eta t T hA hAM heta hxi hden ht htT
    hT hcritical hscale
  exact hAssembly.trans (by nlinarith)

#print axioms pintz2023_low_block_equation423_native
#print axioms pintz2023_middle_block_equation421_native
#print axioms pintz2023_smallB_source_gram_native

end

end GafniTao
