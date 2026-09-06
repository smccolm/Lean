import GafniTao.Pintz2023SourceOrderSelection

/-!
# Pintz (2023), high-zero detected family

This module applies the exact equation-(4.12) detector to the actual
multiplicity-weighted zeros with `2 log T < |Im rho| <= T`, then invokes the
source-order selection.  No sampled zero set or fixed real-part surrogate is
introduced.
-/

open Filter Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's high-zero portion of the near-one rectangle. -/
noncomputable def pintz2023HighZeroSet (eta T : ℝ) : Finset ℂ :=
  (zeroSet (1 - eta) T).filter
    (fun rho => 2 * Real.log T < |rho.im|)

theorem pintz2023HighZeroSet_subset
    (eta T : ℝ) :
    pintz2023HighZeroSet eta T ⊆ zeroSet (1 - eta) T := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

/-- The high zeros yield Pintz's detected, `3 lambda`-separated family with
the exact source-order multiplicity loss. -/
theorem eventually_exists_pintz2023_highZero_detected_family
    {eta epsilon : ℝ} {k ell : ℕ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 24)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1)
    (hkTwo : 2 ≤ k) (hell : 0 < ell)
    (hcutoffExponent : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ))
    (hdecay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0) :
    ∀ᶠ T : ℝ in atTop,
      ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
        IsSeparated (3 * pintz2023SourceLambda T k) W ∧
        (∑ rho ∈ pintz2023HighZeroSet eta T,
            zeroMultiplicity rho) ≤
          (2 * Nat.ceil
            (globalLocalZeroLogConstant * Real.log T)) *
            (2 * (2 * Nat.ceil
              (7 * pintz2023SourceLambda T k) + 1)) * W.card ∧
        (∀ u ∈ W, etaAt u ∈ Set.Icc 0 eta) ∧
        (∀ u ∈ W,
          |u| ≤ T + 2 * pintz2023SourceLambda T k) ∧
        ∀ u ∈ W,
          1 / (32 * Real.exp 2 *
              Real.log (pintz2023SourceLambda T k)) ≤
            ‖pintz2023TruncatedPolynomial
              (pintz2023SourceX T epsilon ell)
              (pintz2023Cutoff (pintz2023SourceLambda T k))
              (1 - etaAt u + 1 / pintz2023SourceLambda T k) u‖ := by
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkTwo
  have hDetector := eventually_exists_pintz2023Equation412_source_detector
    heta hetaUpper hepsilon hepsilon hepsilonUpper hkTwo hell
      hcutoffExponent hdecay
  filter_upwards [hDetector,
    eventually_ge_atTop (max (Real.exp 2) 8)] with T hDetectorT hT
  have hTOne : 1 < T := by
    calc
      (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      _ ≤ max (Real.exp 2) 8 := le_max_left _ _
      _ ≤ T := hT
  have hlambda : 0 < pintz2023SourceLambda T k :=
    pintz2023SourceLambda_pos hTOne hk
  have hsigma : 0 ≤ 1 - eta := by
    linarith
  let S := pintz2023HighZeroSet eta T
  have hS : S ⊆ zeroSet (1 - eta) T := by
    exact pintz2023HighZeroSet_subset eta T
  have hDetected : ∀ rho ∈ S,
      ∃ u : ℝ,
        |rho.im - u| ≤ 2 * pintz2023SourceLambda T k ∧
        1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) ≤
          ‖pintz2023TruncatedPolynomial
            (pintz2023SourceX T epsilon ell)
            (pintz2023Cutoff (pintz2023SourceLambda T k))
            (1 - (1 - rho.re) + 1 / pintz2023SourceLambda T k) u‖ := by
    intro rho hrho
    have hrhoHigh := Finset.mem_filter.mp hrho
    have hdata := mem_zeroSet_data hrhoHigh.1
    have hzeroSetZero : rho ∈ zeroSet 0 T :=
      zeroSet_subset_of_sigma_le hsigma hrhoHigh.1
    have hreLt : rho.re < 1 := re_lt_one_of_mem_zeroSet hzeroSetZero
    have hetaRho : 0 < 1 - rho.re := by linarith
    have hetaRhoUpper : 1 - rho.re ≤ eta := by linarith [hdata.1]
    have himUpper : |rho.im| ≤ T :=
      abs_le.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩
    have hpintz : pintz2023Rho (1 - rho.re) rho.im = rho := by
      apply Complex.ext <;> simp [pintz2023Rho]
    have hzero : riemannZeta
        (pintz2023Rho (1 - rho.re) rho.im) = 0 := by
      rw [hpintz]
      exact hdata.2.2.2.2
    exact hDetectorT (1 - rho.re) rho.im hetaRho hetaRhoUpper
      hrhoHigh.2 himUpper hzero
  obtain ⟨W, etaAt, hSep, hCount, hEtaAt, _hProvenance,
      _hLower, hUpper, hLarge⟩ :=
    exists_pintz2023_source_order_variable_selection_subset
      S hS (by
        intro rho hrho
        exact (Finset.mem_filter.mp hrho).2)
      hsigma hT hlambda hDetected
  exact ⟨W, etaAt, hSep, by simpa only [S] using hCount,
    hEtaAt, hUpper, hLarge⟩

#print axioms pintz2023HighZeroSet_subset
#print axioms eventually_exists_pintz2023_highZero_detected_family

end

end GafniTao
