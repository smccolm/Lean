import GafniTao.Pintz2023PoweredMHH

/-!
# Pintz (2023), equations (4.13)--(4.24): both dyadic selections

This file composes the first source localization of the full truncated
polynomial with the exact powered-block MHH consumer.  The intermediate
family is retained in the conclusion, so the two subset relations and the
two cardinality losses can be audited independently.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Complete finite selection-and-powering bridge from the source truncated
polynomial to one unit-coefficient MHH block. -/
theorem exists_pintz2023_full_powered_mhh_bound
    {X Y h : ℕ} {beta V T epsilonCoeff epsilonMHH : ℝ}
    {W : Finset ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hV : 0 < V)
    (hT : 1 ≤ T) (hEpsilonCoeff : 0 < epsilonCoeff)
    (hEpsilonCoeffBeta : epsilonCoeff ≤ beta)
    (hEpsilonMHH : 0 < epsilonMHH)
    (hScale : ∀ q ∈ Finset.range (pintz2023DyadicDepth Y),
      ∀ r ∈ Finset.range h,
        ((2 ^ r * (2 ^ q * X) ^ h : ℕ) : ℝ) ≤ T)
    (hSeparated : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y beta t‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∃ q ∈ Finset.range (pintz2023DyadicDepth Y),
      ∃ W₀ ⊆ W,
        (W.card : ℝ) ≤ pintz2023DyadicDepth Y * (W₀.card : ℝ) ∧
      ∃ r ∈ Finset.range h, ∃ W₁ ⊆ W₀,
        (W₀.card : ℝ) ≤ h * (W₁.card : ℝ) ∧
        (W.card : ℝ) ≤
          pintz2023DyadicDepth Y * h * (W₁.card : ℝ) ∧
        (W₁.card : ℝ) ≤
          K * T ^ epsilonMHH *
            (((2 ^ r * (2 ^ q * X) ^ h : ℕ) : ℝ) ^ 2 /
                (((V / pintz2023DyadicDepth Y) ^ h / h) / B) ^ 2 +
              T * min
                (((2 ^ r * (2 ^ q * X) ^ h : ℕ) : ℝ) /
                  (((V / pintz2023DyadicDepth Y) ^ h / h) / B) ^ 2)
                (((2 ^ r * (2 ^ q * X) ^ h : ℕ) : ℝ) ^ 4 /
                  (((V / pintz2023DyadicDepth Y) ^ h / h) / B) ^ 6)) := by
  obtain ⟨q, hq, W₀, hW₀, hCard₀, hLarge₀⟩ :=
    exists_pintz2023_dyadic_block_and_subset beta W V hX hLarge
  have hU : 0 < 2 ^ q * X := by
    exact mul_pos (pow_pos (by omega) q) (lt_of_lt_of_le (by omega) hX)
  have hDepthPosReal : (0 : ℝ) < pintz2023DyadicDepth Y := by
    exact_mod_cast pintz2023DyadicDepth_pos Y
  have hV₀ : 0 < V / pintz2023DyadicDepth Y :=
    div_pos hV hDepthPosReal
  have hSep₀ : IsSeparated 1 W₀ := by
    intro s hs t ht hst
    exact hSeparated s (hW₀ hs) t (hW₀ ht) hst
  have hBase₀ : InBaseInterval T W₀ := by
    intro t ht
    exact hBase t (hW₀ ht)
  obtain ⟨B, hB, K, hK, r, hr, W₁, hW₁, hCard₁, hMHH⟩ :=
    exists_pintz2023_powered_mhh_bound
      hU hh hV₀ hT hEpsilonCoeff hEpsilonCoeffBeta hEpsilonMHH
      (fun r hr => hScale q hq r hr) hSep₀ hBase₀ hLarge₀
  have hCombined : (W.card : ℝ) ≤
      pintz2023DyadicDepth Y * h * (W₁.card : ℝ) := by
    calc
      (W.card : ℝ) ≤
          pintz2023DyadicDepth Y * (W₀.card : ℝ) := hCard₀
      _ ≤ pintz2023DyadicDepth Y * (h * (W₁.card : ℝ)) := by
        gcongr
      _ = pintz2023DyadicDepth Y * h * (W₁.card : ℝ) := by ring
  exact ⟨B, hB, K, hK, q, hq, W₀, hW₀, hCard₀,
    r, hr, W₁, hW₁, hCard₁, hCombined, hMHH⟩

/-- Scale-sensitive composition of both dyadic selections.  This is the
finite form that retains Pintz's `Q^beta` saving through the full truncated
source polynomial. -/
theorem exists_pintz2023_full_powered_scaled_mhh_bound
    {X Y h : ℕ} {beta V T epsilonCoeff epsilonMHH : ℝ}
    {W : Finset ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hV : 0 < V)
    (hBeta : 0 ≤ beta) (hT : 1 ≤ T)
    (hEpsilonCoeff : 0 < epsilonCoeff)
    (hEpsilonMHH : 0 < epsilonMHH)
    (hScale : ∀ q ∈ Finset.range (pintz2023DyadicDepth Y),
      ∀ r ∈ Finset.range h,
        ((2 ^ r * (2 ^ q * X) ^ h : ℕ) : ℝ) ≤ T)
    (hSeparated : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖pintz2023TruncatedPolynomial X Y beta t‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∃ q ∈ Finset.range (pintz2023DyadicDepth Y),
      ∃ W₀ ⊆ W,
        (W.card : ℝ) ≤ pintz2023DyadicDepth Y * (W₀.card : ℝ) ∧
      ∃ r ∈ Finset.range h, ∃ W₁ ⊆ W₀,
        let Q : ℕ := 2 ^ r * (2 ^ q * X) ^ h
        let L : ℝ :=
          (Q : ℝ) ^ beta *
              ((V / pintz2023DyadicDepth Y) ^ h / h) /
            (B * ((2 * Q : ℕ) : ℝ) ^ epsilonCoeff)
        (W₀.card : ℝ) ≤ h * (W₁.card : ℝ) ∧
        (W.card : ℝ) ≤
          pintz2023DyadicDepth Y * h * (W₁.card : ℝ) ∧
        (W₁.card : ℝ) ≤
          K * T ^ epsilonMHH *
            ((Q : ℝ) ^ 2 / L ^ 2 +
              T * min ((Q : ℝ) / L ^ 2)
                ((Q : ℝ) ^ 4 / L ^ 6)) := by
  obtain ⟨q, hq, W₀, hW₀, hCard₀, hLarge₀⟩ :=
    exists_pintz2023_dyadic_block_and_subset beta W V hX hLarge
  have hU : 0 < 2 ^ q * X := by
    exact mul_pos (pow_pos (by omega) q) (lt_of_lt_of_le (by omega) hX)
  have hDepthPosReal : (0 : ℝ) < pintz2023DyadicDepth Y := by
    exact_mod_cast pintz2023DyadicDepth_pos Y
  have hV₀ : 0 < V / pintz2023DyadicDepth Y :=
    div_pos hV hDepthPosReal
  have hSep₀ : IsSeparated 1 W₀ := by
    intro s hs t ht hst
    exact hSeparated s (hW₀ hs) t (hW₀ ht) hst
  have hBase₀ : InBaseInterval T W₀ := by
    intro t ht
    exact hBase t (hW₀ ht)
  obtain ⟨B, hB, K, hK, r, hr, W₁, hW₁, hCard₁, hMHH⟩ :=
    exists_pintz2023_powered_scaled_mhh_bound
      hU hh hV₀ hBeta hT hEpsilonCoeff hEpsilonMHH
      (fun r hr => hScale q hq r hr) hSep₀ hBase₀ hLarge₀
  have hCombined : (W.card : ℝ) ≤
      pintz2023DyadicDepth Y * h * (W₁.card : ℝ) := by
    calc
      (W.card : ℝ) ≤
          pintz2023DyadicDepth Y * (W₀.card : ℝ) := hCard₀
      _ ≤ pintz2023DyadicDepth Y * (h * (W₁.card : ℝ)) := by
        gcongr
      _ = pintz2023DyadicDepth Y * h * (W₁.card : ℝ) := by ring
  exact ⟨B, hB, K, hK, q, hq, W₀, hW₀, hCard₀,
    r, hr, W₁, hW₁, hCard₁, hCombined, hMHH⟩

#print axioms exists_pintz2023_full_powered_mhh_bound
#print axioms exists_pintz2023_full_powered_scaled_mhh_bound

end

end GafniTao
