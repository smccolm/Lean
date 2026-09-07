import GafniTao.HeathBrownAtkinsonLambdaScale

/-!
# Explicit height-gap bound for the Atkinson Gram entry

This is the `p = q = 1/2` B-process estimate behind Ivić (7.19), before
dyadic spacing is summed.  Unlike an asymptotic placeholder, the displayed
majorant keeps the physical height gap, the dyadic index, and every numerical
The constant.
-/

namespace GafniTao

noncomputable section

/-- The literal scale `K² sqrt (u/K)` in the curvature of the Atkinson phase.
The shifted argument is the exact left endpoint used by the terminal Gram
block. -/
def heathBrownAtkinsonTerminalScale (u : Real) (K : Nat) : Real :=
  ((K + 1 : Nat) : Real) ^ (2 : Nat) *
    Real.sqrt (u / ((K + 1 : Nat) : Real))

/-- An explicit B-process majorant for a pair of ordered heights. -/
def heathBrownAtkinsonGramGapMajorant
    (K : Nat) (t u : Real) : Real :=
  (4 * (K : Real) * (t - u) /
      heathBrownAtkinsonTerminalScale u K + 2) *
    (10 / Real.sqrt
      ((t - u) / (20 * heathBrownAtkinsonTerminalScale u K)) + 2)

/-- The orientation-free version of the exact gap majorant.  The larger
height is always placed in the first argument of the phase-difference
estimate. -/
def heathBrownAtkinsonSymmetricGramGapMajorant
    (K : Nat) (t u : Real) : Real :=
  if u < t then
    heathBrownAtkinsonGramGapMajorant K t u
  else
    heathBrownAtkinsonGramGapMajorant K u t

theorem heathBrownAtkinsonGramGapMajorant_nonneg
    (K : Nat) {t u : Real} (htu : u ≤ t) :
    0 ≤ heathBrownAtkinsonGramGapMajorant K t u := by
  unfold heathBrownAtkinsonGramGapMajorant
    heathBrownAtkinsonTerminalScale
  positivity

theorem heathBrownAtkinsonSymmetricGramGapMajorant_nonneg
    (K : Nat) (t u : Real) :
    0 ≤ heathBrownAtkinsonSymmetricGramGapMajorant K t u := by
  unfold heathBrownAtkinsonSymmetricGramGapMajorant
  by_cases hut : u < t
  · rw [if_pos hut]
    exact heathBrownAtkinsonGramGapMajorant_nonneg K hut.le
  · rw [if_neg hut]
    exact heathBrownAtkinsonGramGapMajorant_nonneg K (le_of_not_gt hut)

theorem heathBrownAtkinsonTerminalScale_pos
    {u : Real} {K : Nat} (hu : 0 < u) :
    0 < heathBrownAtkinsonTerminalScale u K := by
  unfold heathBrownAtkinsonTerminalScale
  positivity

/-- The exact square-root cancellation used to simplify the B-process
majorant. -/
theorem sqrt_div_self_eq_one_div_sqrt {x : Real} (hx : 0 < x) :
    Real.sqrt x / x = 1 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  apply (div_eq_div_iff hx.ne' hs.ne').2
  simpa only [one_mul] using Real.mul_self_sqrt hx.le

/-- Source-scale form of the exact Atkinson Gram estimate. -/
theorem norm_heathBrownAtkinsonGram_le_gapMajorant_of_lt
    {K : Nat} {t u : Real}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : ((2 * K + 2 : Nat) : Real) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonGramGapMajorant K t u := by
  let Q := heathBrownAtkinsonTerminalScale u K
  let d := t - u
  let lam := heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1)
  let lamUpper :=
    heathBrownAtkinsonBProcessLambdaUpper t u (K + 1) (K - 1)
  have hQ : 0 < Q := heathBrownAtkinsonTerminalScale_pos hu
  have hd : 0 < d := sub_pos.mpr htu
  have hlam : 0 < lam :=
    heathBrownAtkinsonBProcessLambda_pos hu htu (by omega)
  have hlamUpper : 0 < lamUpper :=
    heathBrownAtkinsonBProcessLambdaUpper_pos hu htu (by omega)
  have hlamLower : d / (20 * Q) ≤ lam := by
    simpa only [Q, d, lam, heathBrownAtkinsonTerminalScale,
      mul_assoc] using
      heathBrownAtkinsonBProcessLambda_terminal_lower hu htu hK
  have hlamUpperBound : lamUpper ≤ 4 * d / Q := by
    simpa only [Q, d, lamUpper, heathBrownAtkinsonTerminalScale] using
      heathBrownAtkinsonBProcessLambdaUpper_terminal_upper hu htu hK
  have hraw := norm_heathBrownAtkinsonGram_le_of_lt
    hu htu hK hblock htUpper
  have hKsub : (((K - 1 : Nat) : Real)) ≤ (K : Real) := by
    exact_mod_cast Nat.sub_le K 1
  have hnum :
      (((K - 1 : Nat) : Real)) * lamUpper ≤
        (K : Real) * (4 * d / Q) :=
    mul_le_mul hKsub hlamUpperBound hlamUpper.le (by positivity)
  have hnumNonneg :
      0 ≤ (((K - 1 : Nat) : Real)) * lamUpper := by positivity
  have hden : (1 : Real) ≤ 2 * Real.pi := by
    linarith [Real.pi_gt_three]
  have hfirst :
      (((K - 1 : Nat) : Real)) * lamUpper / (2 * Real.pi) + 2 ≤
        4 * (K : Real) * d / Q + 2 := by
    have hdiv := div_le_self hnumNonneg hden
    calc
      (((K - 1 : Nat) : Real)) * lamUpper / (2 * Real.pi) + 2 ≤
          (((K - 1 : Nat) : Real)) * lamUpper + 2 := by linarith
      _ ≤ (K : Real) * (4 * d / Q) + 2 := by linarith
      _ = 4 * (K : Real) * d / Q + 2 := by ring
  have hlowerPos : 0 < d / (20 * Q) := by positivity
  have hsqrtOrder :
      Real.sqrt (d / (20 * Q)) ≤ Real.sqrt lam :=
    Real.sqrt_le_sqrt hlamLower
  have hinv :
      1 / Real.sqrt lam ≤ 1 / Real.sqrt (d / (20 * Q)) :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hlowerPos) hsqrtOrder
  have hpi : (2 * Real.pi : Real) ≤ 8 := by
    linarith [Real.pi_le_four]
  have hpiTerm :
      2 * Real.pi / Real.sqrt lam ≤
        8 / Real.sqrt (d / (20 * Q)) := by
    calc
      2 * Real.pi / Real.sqrt lam ≤ 8 / Real.sqrt lam :=
        div_le_div_of_nonneg_right hpi (Real.sqrt_nonneg lam)
      _ ≤ 8 / Real.sqrt (d / (20 * Q)) := by
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : Real) ≤ 8)
  have hratio : Real.sqrt lam / lam = 1 / Real.sqrt lam :=
    sqrt_div_self_eq_one_div_sqrt hlam
  have hsecond :
      2 * Real.pi / Real.sqrt lam +
          2 * (Real.sqrt lam / lam + 1) ≤
        10 / Real.sqrt (d / (20 * Q)) + 2 := by
    rw [hratio]
    have hone :
        1 / Real.sqrt lam + 1 ≤
          1 / Real.sqrt (d / (20 * Q)) + 1 := by
      linarith
    calc
      2 * Real.pi / Real.sqrt lam + 2 * (1 / Real.sqrt lam + 1) ≤
          8 / Real.sqrt (d / (20 * Q)) +
            2 * (1 / Real.sqrt (d / (20 * Q)) + 1) := by
        exact add_le_add hpiTerm
          (mul_le_mul_of_nonneg_left hone (by norm_num))
      _ = 10 / Real.sqrt (d / (20 * Q)) + 2 := by ring
  have hproduct := mul_le_mul hfirst hsecond
    (by positivity : 0 ≤ 2 * Real.pi / Real.sqrt lam +
      2 * (Real.sqrt lam / lam + 1))
    (by positivity : 0 ≤ 4 * (K : Real) * d / Q + 2)
  exact hraw.trans (by
    simpa only [Q, d, lam, lamUpper,
      heathBrownAtkinsonGramGapMajorant] using hproduct)

/-- Symmetric source-scale Gram estimate on a common dyadic height block.
The interval hypotheses derive positivity, block containment, and the factor
two comparability used by the analytic estimate. -/
theorem norm_heathBrownAtkinsonGram_le_symmetricGapMajorant
    {K : Nat} {T t u : Real}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : ((2 * K + 2 : Nat) : Real) ≤ T / 2)
    (ht : t ∈ Set.Icc (T / 2) T)
    (hu : u ∈ Set.Icc (T / 2) T)
    (htu : t ≠ u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonSymmetricGramGapMajorant K t u := by
  have htPos : 0 < t := by linarith [ht.1]
  have huPos : 0 < u := by linarith [hu.1]
  have htBlock : ((2 * K + 2 : Nat) : Real) ≤ t :=
    hblock.trans ht.1
  have huBlock : ((2 * K + 2 : Nat) : Real) ≤ u :=
    hblock.trans hu.1
  by_cases hut : u < t
  · rw [heathBrownAtkinsonSymmetricGramGapMajorant, if_pos hut]
    apply norm_heathBrownAtkinsonGram_le_gapMajorant_of_lt
      huPos hut hK huBlock
    linarith [hu.1, ht.2]
  · have htuLt : t < u := lt_of_le_of_ne (le_of_not_gt hut) htu
    rw [heathBrownAtkinsonSymmetricGramGapMajorant, if_neg hut,
      ← norm_heathBrownAtkinsonGram_swap K t u]
    apply norm_heathBrownAtkinsonGram_le_gapMajorant_of_lt
      htPos htuLt hK htBlock
    linarith [ht.1, hu.2]


end

end GafniTao
