import GafniTao.Pintz2023HighZeroSelection
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Pintz (2023): a physical dyadic height shell

Corollary 3 controls a polynomial of length `O(|t|^(2/k))`.  The global
high-zero range only gives `|t| > 2 log T`, so it cannot justify replacing
`|t|` by the ambient height `T`.  We therefore retain the standard dyadic
shell `T/2 < |Im rho| ≤ T`; detector displacement then leaves the selected
ordinates at height greater than `T/4`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023DyadicHeightShell (eta T : ℝ) : Finset ℂ :=
  (zeroSet (1 - eta) T).filter (fun rho => T / 2 < |rho.im|)

theorem pintz2023DyadicHeightShell_subset (eta T : ℝ) :
    pintz2023DyadicHeightShell eta T ⊆ zeroSet (1 - eta) T := by
  intro rho hrho
  exact (Finset.mem_filter.mp hrho).1

theorem eventually_eight_mul_log_le_identity :
    ∀ᶠ T : ℝ in atTop, 8 * Real.log T ≤ T := by
  have hsmall := Real.isLittleO_log_id_atTop.bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with T hsmallT hT
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hsmallT' : Real.log T ≤ (1 / 8 : ℝ) * T := by
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hlog,
      abs_of_nonneg hTnonneg] using hsmallT
  nlinarith

/-- Equation-(4.12) detection on one true dyadic height shell.  In contrast
to the global high-zero selection, the conclusion records the lower physical
height needed by Corollary 3. -/
theorem eventually_exists_pintz2023_shell_detected_family
    {eta epsilon : ℝ} {k ell : ℕ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 32)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1)
    (hkTwo : 2 ≤ k) (hell : 0 < ell)
    (hcutoffExponent : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ))
    (hdecay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0) :
    ∀ᶠ T : ℝ in atTop,
      ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
        IsSeparated (3 * pintz2023SourceLambda T k) W ∧
        (∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho) ≤
          (2 * Nat.ceil
            (globalLocalZeroLogConstant * Real.log T)) *
            (2 * (2 * Nat.ceil
              (7 * pintz2023SourceLambda T k) + 1)) * W.card ∧
        (∀ u ∈ W, etaAt u ∈ Set.Icc 0 eta) ∧
        (∀ u ∈ W, T / 4 < |u|) ∧
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
  filter_upwards [hDetector, eventually_eight_mul_log_le_identity,
    eventually_ge_atTop (max (Real.exp 2) 8)] with T hDetectorT hLogT hT
  have hTOne : 1 < T := by
    calc
      (1 : ℝ) < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      _ ≤ max (Real.exp 2) 8 := le_max_left _ _
      _ ≤ T := hT
  have hlambda : 0 < pintz2023SourceLambda T k :=
    pintz2023SourceLambda_pos hTOne hk
  have hsigma : 0 ≤ 1 - eta := by linarith
  let S := pintz2023DyadicHeightShell eta T
  have hS : S ⊆ zeroSet (1 - eta) T :=
    pintz2023DyadicHeightShell_subset eta T
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
    have hrhoShell := Finset.mem_filter.mp hrho
    have hdata := mem_zeroSet_data hrhoShell.1
    have hzeroSetZero : rho ∈ zeroSet 0 T :=
      zeroSet_subset_of_sigma_le hsigma hrhoShell.1
    have hreLt : rho.re < 1 := re_lt_one_of_mem_zeroSet hzeroSetZero
    have hetaRho : 0 < 1 - rho.re := by linarith
    have hetaRhoUpper : 1 - rho.re ≤ eta := by linarith [hdata.1]
    have himUpper : |rho.im| ≤ T :=
      abs_le.mpr ⟨hdata.2.2.1, hdata.2.2.2.1⟩
    have hgammaLow : 2 * Real.log T < |rho.im| := by
      have : 2 * Real.log T ≤ T / 4 := by linarith
      linarith [hrhoShell.2]
    have hpintz : pintz2023Rho (1 - rho.re) rho.im = rho := by
      apply Complex.ext <;> simp [pintz2023Rho]
    have hzero : riemannZeta
        (pintz2023Rho (1 - rho.re) rho.im) = 0 := by
      rw [hpintz]
      exact hdata.2.2.2.2
    exact hDetectorT (1 - rho.re) rho.im hetaRho hetaRhoUpper
      hgammaLow himUpper hzero
  obtain ⟨W, etaAt, hSep, hCount, hEtaAt, hLower, hUpper, hLarge⟩ :=
    exists_pintz2023_source_order_variable_selection_subset
      S hS (by
        intro rho hrho
        exact (Finset.mem_filter.mp hrho).2)
      hsigma hT hlambda hDetected
  have hLambdaUpper : 2 * pintz2023SourceLambda T k ≤ T / 4 := by
    unfold pintz2023SourceLambda
    have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hkTwo
    have hratio : 2 / (k : ℝ) ≤ 1 := (div_le_one (by positivity)).2 hkReal
    have hlogNonneg : 0 ≤ Real.log T := Real.log_nonneg hTOne.le
    have : pintz2023SourceLambda T k ≤ Real.log T := by
      unfold pintz2023SourceLambda
      nlinarith [mul_le_mul_of_nonneg_right hratio hlogNonneg]
    nlinarith
  have hPhysicalLower : ∀ u ∈ W, T / 4 < |u| := by
    intro u hu
    have := hLower u hu
    linarith
  exact ⟨W, etaAt, hSep, by simpa only [S] using hCount,
    hEtaAt, hPhysicalLower, hUpper, hLarge⟩

#print axioms pintz2023DyadicHeightShell_subset
#print axioms eventually_eight_mul_log_le_identity
#print axioms eventually_exists_pintz2023_shell_detected_family

end

end GafniTao
