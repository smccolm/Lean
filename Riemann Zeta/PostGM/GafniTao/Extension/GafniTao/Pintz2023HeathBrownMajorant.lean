import GafniTao.Pintz2023DerivativeApplication
import GafniTao.FordExponentialSumAbel

/-!
# Pintz (2023), Corollary 1: uniform prefixes and Abel summation

Heath--Brown's Theorem 1 is stated for a sum of its full displayed length.
Pintz's partial summation needs the same estimate for every prefix of
`(N,2N]`.  The outer length power cancels the two negative length powers in
Heath--Brown's three-term factor, so the full-`N` majorant controls every
shorter positive prefix.  This file records that comparison before applying
Abel summation; no abstract bounded-weight replacement is introduced.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- After multiplication by the outer `L^(1+epsilon)`, each of
Heath--Brown's three length powers is monotone for `k >= 3`. -/
theorem heathBrownKthDerivative_length_monotone
    {k : ℕ} {epsilon L N lambda : ℝ}
    (hk : 3 ≤ k) (hepsilon : 0 < epsilon)
    (hL : 1 ≤ L) (hLN : L ≤ N) (hlambda : 0 ≤ lambda) :
    L ^ (1 + epsilon) * heathBrownKthDerivativeFactor k L lambda ≤
      N ^ (1 + epsilon) * heathBrownKthDerivativeFactor k N lambda := by
  have hkReal : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkMinus : (2 : ℝ) ≤ (k : ℝ) - 1 := by linarith
  have hden : 0 < (k : ℝ) * ((k : ℝ) - 1) := by positivity
  have hdenSix : (6 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
  have hN : 1 ≤ N := hL.trans hLN
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  let a : ℝ := 1 / ((k : ℝ) * ((k : ℝ) - 1))
  let b : ℝ := 2 / ((k : ℝ) * ((k : ℝ) - 1))
  let c : ℝ := 2 / ((k : ℝ) ^ 2 * ((k : ℝ) - 1))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have heOne : 0 ≤ 1 + epsilon := by linarith
  have heA : 0 ≤ 1 + epsilon - a := by
    dsimp only [a]
    have haUpper : 1 / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 / 6 := by
      exact one_div_le_one_div_of_le (by norm_num) hdenSix
    linarith
  have heB : 0 ≤ 1 + epsilon - b := by
    dsimp only [b]
    have hbUpper : 2 / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 2 / 6 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hdenSix
    linarith
  have hfirst :
      L ^ (1 + epsilon) * lambda ^ a ≤
        N ^ (1 + epsilon) * lambda ^ a := by
    gcongr
  have hsecond : L ^ (1 + epsilon - a) ≤ N ^ (1 + epsilon - a) :=
    Real.rpow_le_rpow hLPos.le hLN heA
  have hthird :
      L ^ (1 + epsilon - b) * lambda ^ (-c) ≤
        N ^ (1 + epsilon - b) * lambda ^ (-c) := by
    gcongr
  unfold heathBrownKthDerivativeFactor
  have hnegA :
      -1 / ((k : ℝ) * ((k : ℝ) - 1)) = -a := by
    dsimp only [a]
    ring
  have hnegB :
      -2 / ((k : ℝ) * ((k : ℝ) - 1)) = -b := by
    dsimp only [b]
    ring
  have hnegC :
      -2 / ((k : ℝ) ^ 2 * ((k : ℝ) - 1)) = -c := by
    dsimp only [c]
    ring
  rw [hnegA, hnegB, hnegC]
  change L ^ (1 + epsilon) *
      (lambda ^ a + L ^ (-a) + L ^ (-b) * lambda ^ (-c)) ≤
    N ^ (1 + epsilon) *
      (lambda ^ a + N ^ (-a) + N ^ (-b) * lambda ^ (-c))
  rw [mul_add, mul_add, mul_add, mul_add]
  have hLSecond : L ^ (1 + epsilon) * L ^ (-a) =
      L ^ (1 + epsilon - a) := by
    rw [← Real.rpow_add hLPos]
    rw [sub_eq_add_neg]
  have hNSecond : N ^ (1 + epsilon) * N ^ (-a) =
      N ^ (1 + epsilon - a) := by
    rw [← Real.rpow_add hNPos]
    rw [sub_eq_add_neg]
  have hLThird : L ^ (1 + epsilon) * (L ^ (-b) * lambda ^ (-c)) =
      L ^ (1 + epsilon - b) * lambda ^ (-c) := by
    rw [← mul_assoc, ← Real.rpow_add hLPos]
    rw [sub_eq_add_neg]
  have hNThird : N ^ (1 + epsilon) * (N ^ (-b) * lambda ^ (-c)) =
      N ^ (1 + epsilon - b) * lambda ^ (-c) := by
    rw [← mul_assoc, ← Real.rpow_add hNPos]
    rw [sub_eq_add_neg]
  rw [hLSecond, hNSecond, hLThird, hNThird]
  exact add_le_add (add_le_add hfirst hsecond) hthird

/-- The source derivative estimate supplies every positive prefix of
`(N,2N]` with one common full-`N` majorant. -/
theorem norm_pintz2023ExponentialBlock_prefix_le
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N Q : ℕ) (t : ℝ),
      0 < N → N < Q → Q ≤ 2 * N → 0 < t →
      ‖pintz2023ExponentialBlock N Q t‖ ≤
        C * (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N
            (pintz2023DerivativeLambda k N t) := by
  obtain ⟨C, hC, hblock⟩ :=
    norm_pintz2023ExponentialBlock_le_heathBrown k epsilon hk hepsilon
  refine ⟨C, hC, ?_⟩
  intro N Q t hN hNQ hQ ht
  have hLength : 1 ≤ Q - N := by omega
  have hLengthN : Q - N ≤ N := by omega
  have hlambda : 0 ≤ pintz2023DerivativeLambda k N t := by
    unfold pintz2023DerivativeLambda
    positivity
  have hmono := heathBrownKthDerivative_length_monotone hk hepsilon
    (show (1 : ℝ) ≤ (Q - N : ℕ) by exact_mod_cast hLength)
    (show ((Q - N : ℕ) : ℝ) ≤ N by exact_mod_cast hLengthN)
    hlambda
  calc
    ‖pintz2023ExponentialBlock N Q t‖ ≤
        C * (((Q - N : ℕ) : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k (Q - N : ℕ)
            (pintz2023DerivativeLambda k N t)) := by
      simpa [Nat.cast_sub hNQ.le, mul_assoc] using
        hblock N Q t hN hNQ hQ ht
    _ ≤ C * ((N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N
            (pintz2023DerivativeLambda k N t)) :=
      mul_le_mul_of_nonneg_left hmono hC.le
    _ = C * (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor k N
            (pintz2023DerivativeLambda k N t) := by ring

/-- The literal weighted Dirichlet block `H_xi(N)` in Pintz (3.1), with a
general right endpoint inside `(N,2N]`. -/
noncomputable def pintz2023WeightedBlock
    (xi : ℝ) (N R : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N R,
    (n : ℝ) ^ (-(1 - xi)) • (n : ℂ) ^ (-(t : ℂ) * I)

/-- Exact positive-prefix reindexing used by Abel summation. -/
theorem pintz2023ExponentialBlock_eq_sum_range
    (N j : ℕ) (t : ℝ) :
    pintz2023ExponentialBlock N (N + j) t =
      ∑ i ∈ Finset.range j,
        (N + 1 + i : ℂ) ^ (-(t : ℂ) * I) := by
  unfold pintz2023ExponentialBlock
  have hIoc : Finset.Ioc N (N + j) =
      Finset.Ico (N + 1) (N + j + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  have hLength : N + j + 1 - (N + 1) = j := by omega
  rw [hLength]
  simp only [Nat.cast_add, Nat.cast_one]

/-- Pintz's exact partial-summation step, retaining the source endpoint
weight `(N+1)^(-(1-xi))` and the complete three-term derivative factor. -/
theorem norm_pintz2023WeightedBlock_le_heathBrown
    (k : ℕ) (epsilon xi : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon)
    (hxi : xi ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (t : ℝ),
      0 < N → N < R → R ≤ 2 * N → 0 < t →
      ‖pintz2023WeightedBlock xi N R t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-(1 - xi)) *
          (C * (N : ℝ) ^ (1 + epsilon) *
            heathBrownKthDerivativeFactor k N
              (pintz2023DerivativeLambda k N t)) := by
  obtain ⟨C, hC, hprefix⟩ :=
    norm_pintz2023ExponentialBlock_prefix_le k epsilon hk hepsilon
  refine ⟨C, hC, ?_⟩
  intro N R t hN hNR hR ht
  unfold pintz2023WeightedBlock
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => (n : ℝ) ^ (-(1 - xi)))
      (fun n => (n : ℂ) ^ (-(t : ℂ) * I)) N R
      (C * (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N
          (pintz2023DerivativeLambda k N t)) hNR
  · intro n hn
    exact Real.rpow_nonneg (by positivity) _
  · intro n hnN hnR
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (show 0 < n by omega)
    · exact_mod_cast Nat.le_succ n
    · exact neg_nonpos.mpr (sub_nonneg.mpr hxi)
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Finset.range_zero, sum_empty, norm_zero]
      have hlambda : 0 < pintz2023DerivativeLambda k N t := by
        unfold pintz2023DerivativeLambda
        positivity
      exact mul_nonneg
        (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
        (heathBrownKthDerivativeFactor_nonneg k (by positivity) hlambda)
    · simp_rw [Nat.cast_add, Nat.cast_one]
      rw [← pintz2023ExponentialBlock_eq_sum_range]
      exact hprefix N (N + j) t hN (by omega) (by omega) ht

#print axioms heathBrownKthDerivative_length_monotone
#print axioms norm_pintz2023ExponentialBlock_prefix_le
#print axioms pintz2023ExponentialBlock_eq_sum_range
#print axioms norm_pintz2023WeightedBlock_le_heathBrown

end

end GafniTao
