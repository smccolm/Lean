import GafniTao.Pintz2023GramCutoff

/-!
# Pintz (2023), transport of equation (4.23) to `A_h`

The low-shell estimate must retain Corollary 2's exact first exponent until
the shell is transported to the powered endpoint.  At that endpoint the
critical-scale inequality turns both Corollary-2 monomials into
`A_h^(-3 epsilon)`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

private theorem mul_div_rpow_le_rpow
    {x y p : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (hp : -1 ≤ p) :
    (x / y) * x ^ p ≤ y ^ p := by
  have hpOne : 0 ≤ p + 1 := by linarith
  have hpow := Real.rpow_le_rpow hx.le hxy hpOne
  calc
    (x / y) * x ^ p = x ^ (p + 1) / y := by
      rw [Real.rpow_add hx, Real.rpow_one]
      field_simp
    _ ≤ y ^ (p + 1) / y := div_le_div_of_nonneg_right hpow hy.le
    _ = y ^ p := by
      rw [Real.rpow_add hy, Real.rpow_one]
      field_simp

/-- Exact low-shell majorant before the source endpoint is applied. -/
noncomputable def pintz2023LowGramRawShellMajorant
    (C t eta epsilon xi : ℝ) (r A j : ℕ) : ℝ :=
  let L : ℕ := 2 ^ j
  let R : ℕ := min A (2 ^ (j + 1))
  C * ((L : ℝ) / A) * (R : ℝ) ^ (4 * eta) *
    pintz2023CorollaryTwoMajorant r L epsilon xi t

/-- A low shell is bounded by the exact pre-simplification form of (4.23). -/
theorem pintz2023_low_block_equation423_raw_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ) (xi eta t : ℝ),
        0 < A → 0 ≤ eta → 0 < t →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        (A : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023HalaszKernelWeightedBlock A (xi + 4 * eta) 1 A t‖ ≤
          ∑ j ∈ Finset.range (Nat.clog 2 A),
            pintz2023LowGramRawShellMajorant C t eta epsilon xi r A j := by
  obtain ⟨C, hC, h423⟩ :=
    pintz2023_equation423_shift_four_eta_raw_native
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
  have h := h423 A L R xi eta t hA hL hLR hRtwo hRA heta ht hxi hLscale
  simpa only [pintz2023LowGramRawShellMajorant, L, R] using h

/-- The exact Corollary-2 majorant at `A_h` is at most twice the source
power saving once `A_h` is beyond the critical scale. -/
theorem pintz2023_corollaryTwoMajorant_at_critical_le
    {r A : ℕ} {epsilon xi t T : ℝ}
    (hr : 3 ≤ r) (hepsilon : 0 < epsilon) (hA : 0 < A)
    (ht : 0 < t) (htT : t ≤ T) (hT : 1 ≤ T)
    (hden : 0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon)
    (hcritical : pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ)) :
    pintz2023CorollaryTwoMajorant r A epsilon xi t ≤
      2 * (A : ℝ) ^ (-3 * epsilon) := by
  have hfirst := pintz2023_first_term_le_of_critical_scale
    hr hepsilon hA ht htT hT hden hcritical
  unfold pintz2023CorollaryTwoMajorant
  linarith

/-- The endpoint transport used after (4.23).  Both powers are monotone only
after the factor `L/A` from the exact Halasz kernel has been retained. -/
theorem pintz2023_low_raw_shell_majorant_le_endpoint
    {r A L R : ℕ} {C t eta epsilon xi T : ℝ}
    (hr : 3 ≤ r) (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hepsilonUpper : 3 * epsilon ≤ 1)
    (hA : 0 < A) (hL : 0 < L) (hLA : L ≤ A) (hRA : R ≤ A)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (ht : 0 < t) (htT : t ≤ T) (hT : 1 ≤ T)
    (hden : 0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon)
    (hcritical : pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ)) :
    C * ((L : ℝ) / A) * (R : ℝ) ^ (4 * eta) *
        pintz2023CorollaryTwoMajorant r L epsilon xi t ≤
      2 * C * (A : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon) := by
  have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrSub : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hAReal : (0 : ℝ) < A := by exact_mod_cast hA
  have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
  have hLAReal : (L : ℝ) ≤ A := by exact_mod_cast hLA
  have hRAReal : (R : ℝ) ≤ A := by exact_mod_cast hRA
  let p : ℝ := xi - 1 / ((r : ℝ) - 1) + 3 * epsilon
  have hp : -1 ≤ p := by
    dsimp only [p]
    have hinv : 1 / ((r : ℝ) - 1) ≤ 1 / 2 := by
      exact (div_le_iff₀ hrSub).2 (by nlinarith)
    nlinarith
  have hneg : -1 ≤ -3 * epsilon := by linarith
  have hfirstTransport :
      ((L : ℝ) / A) * ((L : ℝ) ^ p * t ^ pintz2023HBAlpha r) ≤
        (A : ℝ) ^ p * t ^ pintz2023HBAlpha r := by
    have hcore := mul_div_rpow_le_rpow hLReal hAReal hLAReal hp
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hcore
        (Real.rpow_nonneg ht.le (pintz2023HBAlpha r))
  have hsecondTransport :
      ((L : ℝ) / A) * (L : ℝ) ^ (-3 * epsilon) ≤
        (A : ℝ) ^ (-3 * epsilon) :=
    mul_div_rpow_le_rpow hLReal hAReal hLAReal hneg
  have hCorTransport :
      ((L : ℝ) / A) *
          pintz2023CorollaryTwoMajorant r L epsilon xi t ≤
        pintz2023CorollaryTwoMajorant r A epsilon xi t := by
    unfold pintz2023CorollaryTwoMajorant
    change ((L : ℝ) / A) * ((L : ℝ) ^ p * t ^ pintz2023HBAlpha r +
        (L : ℝ) ^ (-3 * epsilon)) ≤
      (A : ℝ) ^ p * t ^ pintz2023HBAlpha r +
        (A : ℝ) ^ (-3 * epsilon)
    nlinarith
  have hRpow : (R : ℝ) ^ (4 * eta) ≤ (A : ℝ) ^ (4 * eta) :=
    Real.rpow_le_rpow (Nat.cast_nonneg R) hRAReal (by positivity)
  have hAt := pintz2023_corollaryTwoMajorant_at_critical_le
    hr hepsilon hA ht htT hT hden hcritical
  have hCorNonneg : 0 ≤ pintz2023CorollaryTwoMajorant r L epsilon xi t := by
    unfold pintz2023CorollaryTwoMajorant
    positivity
  calc
    C * ((L : ℝ) / A) * (R : ℝ) ^ (4 * eta) *
        pintz2023CorollaryTwoMajorant r L epsilon xi t =
      C * (R : ℝ) ^ (4 * eta) *
        (((L : ℝ) / A) *
          pintz2023CorollaryTwoMajorant r L epsilon xi t) := by ring
    _ ≤ C * (A : ℝ) ^ (4 * eta) *
        pintz2023CorollaryTwoMajorant r A epsilon xi t := by gcongr
    _ ≤ C * (A : ℝ) ^ (4 * eta) *
        (2 * (A : ℝ) ^ (-3 * epsilon)) := by gcongr
    _ = 2 * C * (A : ℝ) ^ (4 * eta) *
        (A : ℝ) ^ (-3 * epsilon) := by ring

/-- The complete low block `(1,A_h]`, including its exact number of dyadic
shells, has the endpoint bound used in Pintz's small-`B_h` argument. -/
theorem pintz2023_low_raw_shell_sum_le_endpoint
    {r A : ℕ} {C t eta epsilon xi T : ℝ}
    (hr : 3 ≤ r) (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hepsilonUpper : 3 * epsilon ≤ 1)
    (hA : 0 < A) (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (ht : 0 < t) (htT : t ≤ T) (hT : 1 ≤ T)
    (hden : 0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon)
    (hcritical : pintz2023CriticalScale r xi epsilon T ≤ (A : ℝ)) :
    (∑ j ∈ Finset.range (Nat.clog 2 A),
        pintz2023LowGramRawShellMajorant C t eta epsilon xi r A j) ≤
      (Nat.clog 2 A : ℝ) *
        (2 * C * (A : ℝ) ^ (4 * eta) *
          (A : ℝ) ^ (-3 * epsilon)) := by
  calc
    (∑ j ∈ Finset.range (Nat.clog 2 A),
        pintz2023LowGramRawShellMajorant C t eta epsilon xi r A j) ≤
      ∑ _j ∈ Finset.range (Nat.clog 2 A),
        (2 * C * (A : ℝ) ^ (4 * eta) *
          (A : ℝ) ^ (-3 * epsilon)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjlt : j < Nat.clog 2 A := Finset.mem_range.mp hj
      let L : ℕ := 2 ^ j
      let R : ℕ := min A (2 ^ (j + 1))
      have hL : 0 < L := by dsimp only [L]; positivity
      have hLA : L ≤ A := (Nat.pow_lt_of_lt_clog hjlt).le
      have hRA : R ≤ A := by dsimp only [R]; exact min_le_left _ _
      simpa only [pintz2023LowGramRawShellMajorant, L, R] using
        pintz2023_low_raw_shell_majorant_le_endpoint hr hC hepsilon
          hepsilonUpper hA hL hLA hRA heta hxi ht htT hT hden hcritical
    _ = _ := by simp

/-- Every relative middle shell is bounded at the two source endpoints:
`R ≤ M` controls the inserted `n^(4 eta)`, while `A ≤ L` controls the
negative saving from (4.21). -/
theorem pintz2023_middle_gram_shell_majorant_le
    {A M j : ℕ} {C eta epsilon : ℝ}
    (hC : 0 ≤ C) (heta : 0 ≤ eta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) :
    pintz2023MiddleGramShellMajorant C eta epsilon A M j ≤
      C * (M : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon) := by
  let L : ℕ := 2 ^ j * A
  let R : ℕ := min M (2 ^ (j + 1) * A)
  by_cases hLM : L < M
  · have hAReal : (0 : ℝ) < A := by exact_mod_cast hA
    have hAL : (A : ℝ) ≤ L := by
      exact_mod_cast (show A ≤ L by
        dsimp only [L]
        simpa only [one_mul] using Nat.mul_le_mul_right A
          (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))))
    have hRM : (R : ℝ) ≤ M := by
      exact_mod_cast (show R ≤ M by dsimp only [R]; exact min_le_left _ _)
    have hRpow : (R : ℝ) ^ (4 * eta) ≤ (M : ℝ) ^ (4 * eta) :=
      Real.rpow_le_rpow (Nat.cast_nonneg R) hRM (by positivity)
    have hLpow : (L : ℝ) ^ (-3 * epsilon) ≤
        (A : ℝ) ^ (-3 * epsilon) :=
      Real.rpow_le_rpow_of_nonpos hAReal hAL (by linarith)
    simp only [pintz2023MiddleGramShellMajorant, L, if_pos hLM]
    gcongr
  · simp only [pintz2023MiddleGramShellMajorant, L, if_neg hLM]
    positivity

/-- Exact shell-count version of the middle contribution. -/
theorem pintz2023_middle_gram_shell_sum_le
    {A M : ℕ} {C eta epsilon : ℝ}
    (hC : 0 ≤ C) (heta : 0 ≤ eta) (hepsilon : 0 < epsilon)
    (hA : 0 < A) :
    (∑ j ∈ Finset.range (Nat.clog 2 M),
        pintz2023MiddleGramShellMajorant C eta epsilon A M j) ≤
      (Nat.clog 2 M : ℝ) *
        (C * (M : ℝ) ^ (4 * eta) * (A : ℝ) ^ (-3 * epsilon)) := by
  calc
    (∑ j ∈ Finset.range (Nat.clog 2 M),
        pintz2023MiddleGramShellMajorant C eta epsilon A M j) ≤
      ∑ _j ∈ Finset.range (Nat.clog 2 M),
        (C * (M : ℝ) ^ (4 * eta) *
          (A : ℝ) ^ (-3 * epsilon)) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact pintz2023_middle_gram_shell_majorant_le hC heta hepsilon hA
    _ = _ := by simp

#print axioms pintz2023_low_block_equation423_raw_native
#print axioms pintz2023_corollaryTwoMajorant_at_critical_le
#print axioms pintz2023_low_raw_shell_majorant_le_endpoint
#print axioms pintz2023_low_raw_shell_sum_le_endpoint
#print axioms pintz2023_middle_gram_shell_majorant_le
#print axioms pintz2023_middle_gram_shell_sum_le

end

end GafniTao
