import GafniTao.Pintz2023HalaszAssembly

/-!
# Pintz (2023), small-`B_h` Gram decomposition

This is the exact analytic assembly behind the small-`B_h` branch following
(4.21).  Shells below the critical scale use (4.23); all remaining shells
use (4.21).  The terminal shell and complete exponential tail are retained.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal shell majorant obtained by splitting at Pintz's critical
scale. -/
noncomputable def pintz2023SmallBGramShellMajorant
    (C T t xi eta epsilon : ℝ) (r N M j : ℕ) : ℝ :=
  let L : ℕ := 2 ^ j
  let R : ℕ := min M (2 ^ (j + 1))
  if (L : ℝ) < pintz2023CriticalScale r xi epsilon T then
    C * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
      (L : ℝ) ^ (-3 * epsilon) *
        (1 + t ^ pintz2023HBAlpha r /
          (L : ℝ) ^ (1 / (r : ℝ)))
  else
    C * (R : ℝ) ^ (4 * eta) * (L : ℝ) ^ (-3 * epsilon)

/-- Complete small-`B_h` Gram bound before exponent absorption.  Every
right-hand term is explicit: the `n=1` endpoint, each source shell, and the
first-omitted geometric tail. -/
theorem pintz2023_smallB_complete_gram_native
    (r : ℕ) (epsilon B : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N M : ℕ) (xi eta t T : ℝ),
        0 < N → 1 ≤ M → 0 ≤ eta →
        0 ≤ 1 - (xi + 4 * eta) →
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi - 6 * (r : ℝ) * epsilon →
        0 < t → t ≤ T → 1 ≤ T →
        2 * pintz2023CriticalScale r xi epsilon T ≤ (N : ℝ) →
        (M : ℝ) ≤ B * t ^ (2 / (r : ℝ)) →
        ‖pintz2023SmoothedZetaSum N
            (((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          ‖pintz2023SmoothedZetaTerm N
              (((1 - (xi + 4 * eta) : ℝ) : ℂ) + I * (t : ℂ)) 1‖ +
            (∑ j ∈ Finset.range (Nat.clog 2 M),
              pintz2023SmallBGramShellMajorant
                C T t xi eta epsilon r N M j) +
            Real.exp (-((M + 1 : ℕ) : ℝ) / (2 * N)) *
              (1 - Real.exp (-(1 : ℝ) / (2 * N)))⁻¹ := by
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    pintz2023_equation423_shift_four_eta_native
      r epsilon B hr hepsilon hB
  obtain ⟨Cmiddle, hCmiddle, hmiddle⟩ :=
    pintz2023_equation421_kernel_block_native
      r epsilon B hr hepsilon hB
  let C : ℝ := max Csmall Cmiddle
  have hC : 0 < C := hCsmall.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N M xi eta t T hN hM heta hreal hxi hden ht htT hT
    hcriticalN hMscale
  apply norm_pintz2023SmoothedZetaSum_le_of_shell_majorants
    hN hM hreal
  intro j hj
  let L : ℕ := 2 ^ j
  let R : ℕ := min M (2 ^ (j + 1))
  have hLM : L < M := by
    dsimp only [L]
    exact Nat.pow_lt_of_lt_clog hj
  have hL : 0 < L := by dsimp only [L]; positivity
  have hLR : L < R := by
    dsimp only [R]
    apply lt_min hLM
    dsimp only [L]
    have hpow : 2 ^ j < 2 ^ (j + 1) := by
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    exact hpow
  have hRtwo : R ≤ 2 * L := by
    dsimp only [R, L]
    refine (min_le_right M (2 ^ (j + 1))).trans_eq ?_
    rw [pow_succ, mul_comm]
  have hRleM : R ≤ M := by dsimp only [R]; exact min_le_left _ _
  have hLscale : (L : ℝ) ≤ B * t ^ (2 / (r : ℝ)) := by
    have hLMReal : (L : ℝ) ≤ M := by exact_mod_cast hLM.le
    exact hLMReal.trans hMscale
  rw [show pintz2023SmallBGramShellMajorant
      C T t xi eta epsilon r N M j =
      if (L : ℝ) < pintz2023CriticalScale r xi epsilon T then
        C * ((L : ℝ) / N) * (R : ℝ) ^ (4 * eta) *
          (L : ℝ) ^ (-3 * epsilon) *
            (1 + t ^ pintz2023HBAlpha r /
              (L : ℝ) ^ (1 / (r : ℝ)))
      else
        C * (R : ℝ) ^ (4 * eta) *
          (L : ℝ) ^ (-3 * epsilon) by
        simp only [pintz2023SmallBGramShellMajorant, L, R]]
  split_ifs with hbelow
  · have hRN : R ≤ N := by
      have hRReal : (R : ℝ) ≤ 2 * (L : ℝ) := by
        exact_mod_cast hRtwo
      have hLcrit : 2 * (L : ℝ) <
          2 * pintz2023CriticalScale r xi epsilon T := by linarith
      exact_mod_cast (hRReal.trans (hLcrit.le.trans hcriticalN))
    have hs := hsmall N L R xi eta t hN hL hLR hRtwo hRN
      heta ht hxi hLscale
    exact hs.trans (by
      gcongr
      exact le_max_left Csmall Cmiddle)
  · have hcritL : pintz2023CriticalScale r xi epsilon T ≤ (L : ℝ) :=
      le_of_not_gt hbelow
    have hm := hmiddle N L R xi eta t T hN hL hLR hRtwo heta hxi
      hden ht htT hT hcritL hLscale
    exact hm.trans (by
      gcongr
      exact le_max_right Csmall Cmiddle)

#print axioms pintz2023_smallB_complete_gram_native

end

end GafniTao
