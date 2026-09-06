import GafniTao.Pintz2023DyadicDepthBound
import GafniTao.Pintz2023DyadicHeightShell
import GafniTao.Pintz2023ShiftedEta
import GafniTao.Pintz2023SmallMSupport

/-!
# Pintz (2023), equation (4.15)

This module assembles the detector, the first common dyadic block, the exact
large-`m`/small-`m` coefficient split, the localized Corollary 3 estimate, and
the logarithmic error absorption.  Its conclusion is the literal surviving
small-`m` block for a common subfamily of displaced ordinates.
-/

open Complex Finset Filter
open scoped BigOperators Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The exact scale support and surviving small-`m` lower bound attached to
one selected ordinate in Pintz equation (4.15). -/
def Pintz2023Equation415Block
    (T eta epsilon : ℝ) (k ell r : ℕ)
    (etaAt : ℝ → ℝ) (u : ℝ) : Prop :=
  (((2 ^ r * pintz2023SourceX T epsilon ell : ℕ) : ℝ) <
      (pintz2023SourceX T epsilon ell : ℝ) *
        pintz2023CriticalScale k eta epsilon (2 * T)) ∧
  (1 / (32 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k)) /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2 ≤
      ‖pintz2023SplitIntervalBlock
        (fun n => pintz2023SmallMCoeff
          (pintz2023SourceX T epsilon ell) n
          (pintz2023CriticalScale k eta epsilon (2 * T)))
        (pintz2023LocalizedInterval
          (pintz2023SourceX T epsilon ell)
          (pintz2023Cutoff (pintz2023SourceLambda T k)) r)
        (((1 - etaAt u + 1 / pintz2023SourceLambda T k : ℝ) : ℂ) +
          I * (u : ℂ))‖

/-- Source-faithful equation (4.15) on one physical height shell. -/
theorem eventually_exists_pintz2023_equation415_shell_family
    {eta epsilon : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (hetaUpper : eta ≤ 1 / 24)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1)
    (hcutoffExponent : epsilon / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ))
    (hdecay : pintz2023DetectorExponent eta epsilon epsilon k ell < 0)
    (hAlpha : eta + 6 * epsilon < pintz2023HBAlpha k)
    (hmargin : 6 * (k : ℝ) * epsilon <
      1 - ((k : ℝ) - 1) * eta) :
    ∀ᶠ T : ℝ in atTop,
      ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
      ∃ r ∈ Finset.range
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))),
      ∃ W' ⊆ W,
        IsSeparated (3 * pintz2023SourceLambda T k) W ∧
        (∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho) ≤
          (2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
            (2 * (2 * Nat.ceil
              (7 * pintz2023SourceLambda T k) + 1)) * W.card ∧
        (W.card : ℝ) ≤
          pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
            (W'.card : ℝ) ∧
        (∀ u ∈ W', etaAt u ∈ Set.Icc 0 eta) ∧
        (∀ u ∈ W', T / 4 < |u|) ∧
        (∀ u ∈ W',
          |u| ≤ T + 2 * pintz2023SourceLambda T k) ∧
        ∀ u ∈ W',
          Pintz2023Equation415Block T eta epsilon k ell r etaAt u := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hkTwo : 2 ≤ k := hcell.1.trans' (by omega)
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hDetected := eventually_exists_pintz2023_shell_detected_family
    heta hetaUpper hepsilon hepsilonUpper hkTwo hell hcutoffExponent hdecay
  have hLargeM := eventually_pintz2023_largeM_localized_le
    hcell hepsilon hAlpha hmargin
  have hError :=
    eventually_pintz2023_largeM_error_le_half_localized_threshold
      hepsilon hkTwo
  have hShiftedEta :=
    eventually_pintz2023_shifted_eta_pos_on_shell_of_le_half
      (hetaUpper.trans (by norm_num)) (lt_of_lt_of_le (by omega) hkTwo)
  have hk : 0 < k := lt_of_lt_of_le (by omega) hkTwo
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  filter_upwards [hDetected, hLargeM, hError, hShiftedEta,
    eventually_ge_atTop 1,
    hLambda.eventually (eventually_gt_atTop 1)] with
      T hDetectedT hLargeMT hErrorT hShiftedEtaT hT hLambdaT
  obtain ⟨W, etaAt, hSeparated, hCount, hEtaAt, hProvenance,
      hPhysical, hUpper, hDetector⟩ := hDetectedT
  have hX : 1 ≤ pintz2023SourceX T epsilon ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hT (by positivity)
  let V : ℝ := 1 / (32 * Real.exp 2 *
    Real.log (pintz2023SourceLambda T k))
  obtain ⟨r, hr, W', hW', hCard, hFull⟩ :=
    exists_pintz2023_variable_dyadic_block_and_subset
      W V
      (fun u => 1 - etaAt u + 1 / pintz2023SourceLambda T k)
      (fun u => u) hX (by
        intro u hu
        simpa only [V] using hDetector u hu)
  refine ⟨W, etaAt, r, hr, W', hW', hSeparated, hCount, hCard,
    ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hEtaAt u (hW' hu)
  · intro u hu
    exact hPhysical u (hW' hu)
  · intro u hu
    exact hUpper u (hW' hu)
  · intro u hu
    let Iset := pintz2023LocalizedInterval
      (pintz2023SourceX T epsilon ell)
      (pintz2023Cutoff (pintz2023SourceLambda T k)) r
    let s : ℂ :=
      ((1 - etaAt u + 1 / pintz2023SourceLambda T k : ℝ) : ℂ) +
        I * (u : ℂ)
    have hLogLambda : 0 <
        Real.log (pintz2023SourceLambda T k) := Real.log_pos hLambdaT
    have hDepthPos : 0 < pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)) :=
      pintz2023DyadicDepth_pos _
    have hVPos : 0 < V := by
      dsimp only [V]
      positivity
    have hLocalizedPositive : 0 < V /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) := by
      positivity
    have hFullU : V /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k)) ≤
        ‖pintz2023IntervalBlock
          (pintz2023SourceX T epsilon ell) Iset s‖ := by
      simpa only [Iset, s] using hFull u hu
    have hNonempty : Iset.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hFullU
      simp [pintz2023IntervalBlock] at hFullU
      linarith
    have hEndpoint : 2 ^ r * pintz2023SourceX T epsilon ell ≤
        min (2 * (2 ^ r * pintz2023SourceX T epsilon ell))
          (pintz2023Cutoff (pintz2023SourceLambda T k)) + 1 := by
      exact pintz2023LocalizedInterval_left_le_right_add_one_of_nonempty
        (by simpa only [Iset] using hNonempty)
    obtain ⟨rho, hrho, hEtaEq, _hDisplacement⟩ :=
      hProvenance u (hW' hu)
    have hShiftedPos : 0 <
        etaAt u - 1 / pintz2023SourceLambda T k := by
      rw [hEtaEq]
      linarith [hShiftedEtaT rho hrho]
    have hShiftedUpper :
        etaAt u - 1 / pintz2023SourceLambda T k ≤ eta := by
      have hInvPos : 0 < 1 / pintz2023SourceLambda T k := by positivity
      linarith [(hEtaAt u (hW' hu)).2]
    have hLargeU := hLargeMT
      (etaAt u - 1 / pintz2023SourceLambda T k) u r
      hShiftedPos.le hShiftedUpper
      (hPhysical u (hW' hu)) (hUpper u (hW' hu)) hEndpoint
    have hComplexEq :
        (((1 - etaAt u + 1 / pintz2023SourceLambda T k : ℝ) : ℂ) +
            I * (u : ℂ)) =
          (((1 - (etaAt u - 1 / pintz2023SourceLambda T k) : ℝ) : ℂ) +
            I * (u : ℂ)) := by
      push_cast
      ring
    have hSmall := pintz2023_smallM_survives_half
      (pintz2023SourceX T epsilon ell)
      (pintz2023CriticalScale k eta epsilon (2 * T)) Iset s
      (V / pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)))
      (T ^ (-2 * epsilon / (k : ℝ))) hFullU
      (by
        rw [show s =
          (((1 - (etaAt u - 1 / pintz2023SourceLambda T k) : ℝ) : ℂ) +
            I * (u : ℂ)) by exact hComplexEq]
        simpa only [Iset] using hLargeU) (by
        simpa only [V] using hErrorT)
    unfold Pintz2023Equation415Block
    refine ⟨?_, by simpa only [V, Iset, s] using hSmall⟩
    apply pintz2023LocalizedSmallMBlock_left_lt_scale
      (R := pintz2023CriticalScale k eta epsilon (2 * T))
      (V := V / pintz2023DyadicDepth
        (pintz2023Cutoff (pintz2023SourceLambda T k)) / 2)
      (s := s)
    · exact (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * T) _).le
    · positivity
    · simpa only [Iset] using hSmall

#print axioms eventually_exists_pintz2023_equation415_shell_family

end

end GafniTao
