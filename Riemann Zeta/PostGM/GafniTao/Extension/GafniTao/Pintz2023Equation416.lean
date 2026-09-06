import GafniTao.Pintz2023SmallMSecondLocalization

/-!
# Pintz (2023), equation (4.16)

This module assembles the exact first surviving block, the physical
logarithmic scale, the bounded power choice, and the second common dyadic
localization.  The empty selected family is retained as an explicit branch.
-/

open Complex Finset Filter
open scoped Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Source-faithful equation (4.16) on one physical height shell. -/
theorem eventually_exists_pintz2023_equation416_shell_family
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∀ᶠ T : ℝ in atTop,
      ∃ W : Finset ℝ, ∃ etaAt : ℝ → ℝ,
      ∃ r ∈ Finset.range
          (pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))),
      ∃ W₁ ⊆ W,
        IsSeparated (3 * pintz2023SourceLambda T k) W ∧
        (∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho) ≤
          (2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
            (2 * (2 * Nat.ceil
              (7 * pintz2023SourceLambda T k) + 1)) * W.card ∧
        (W.card : ℝ) ≤
          pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
            (W₁.card : ℝ) ∧
        (∀ u ∈ W₁, etaAt u ∈ Set.Icc 0 eta) ∧
        (∀ u ∈ W₁, T / 4 < |u|) ∧
        (∀ u ∈ W₁,
          |u| ≤ T + 2 * pintz2023SourceLambda T k) ∧
        (W₁ = ∅ ∨
          ∃ h : ℕ, ∃ q ∈ Finset.range h, ∃ W₂ ⊆ W₁,
            ((2 ^ r * pintz2023SourceX T data.epsilon ell : ℕ) : ℝ) <
              (pintz2023SourceX T data.epsilon ell : ℝ) *
                (2 * T) ^
                  pintz2023CriticalScaleExponent k eta data.epsilon ∧
            2 ≤ h ∧ (h : ℝ) < 20 / data.epsilon ∧
            pintz2023EllThreshold eta data.epsilon ell <
              (h : ℝ) * pintz2023LogScale T
                (2 ^ r * pintz2023SourceX T data.epsilon ell) ∧
            (h = 2 ∨
              (h : ℝ) * pintz2023LogScale T
                  (2 ^ r * pintz2023SourceX T data.epsilon ell) <
                pintz2023EllPowerWindowUpper eta data.epsilon ell) ∧
            (W₁.card : ℝ) ≤ h * (W₂.card : ℝ) ∧
            ∀ u ∈ W₂,
              ((1 / (32 * Real.exp 2 *
                    Real.log (pintz2023SourceLambda T k)) /
                  pintz2023DyadicDepth
                    (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h /
                    h ≤
                ‖dirichletPoly
                  (2 ^ q *
                    (2 ^ r * pintz2023SourceX T data.epsilon ell) ^ h)
                  (pintz2023SmallMPoweredLineCoeff
                    (pintz2023SourceX T data.epsilon ell)
                    (pintz2023CriticalScale
                      k eta data.epsilon (2 * T))
                    (pintz2023LocalizedInterval
                      (pintz2023SourceX T data.epsilon ell)
                      (pintz2023Cutoff (pintz2023SourceLambda T k)) r)
                    h
                    (1 - etaAt u +
                      1 / pintz2023SourceLambda T k)) u‖) := by
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  have hell : 0 < ell := lt_of_lt_of_le (by omega) hcell.2.1
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have h415 := eventually_exists_pintz2023_equation415_shell_family
    hcell data.eta_le_one_twentyFour data.epsilon_pos data.epsilon_le_one
      data.cutoff_exponent data.detector_decay data.k_alpha data.k_margin
  have hLower := eventually_pintz2023_dyadic_logScale_lower
    data.epsilon_pos (lt_of_lt_of_le (by omega) hcell.2.1)
  have hFactor := eventually_two_rpow_lt_rpow data.delta_pos
    (c := pintz2023CriticalScaleExponent k eta data.epsilon)
  have hLambda : Tendsto (fun T : ℝ => pintz2023SourceLambda T k)
      atTop atTop := by
    unfold pintz2023SourceLambda
    exact Real.tendsto_log_atTop.const_mul_atTop
      (div_pos (by norm_num) hkReal)
  filter_upwards [h415, hLower, hFactor, eventually_gt_atTop 1,
    hLambda.eventually (eventually_gt_atTop 1)] with
      T h415T hLowerT hFactorT hT hLambdaT
  obtain ⟨W, etaAt, r, hr, W₁, hW₁, hSeparated, hCount, hCard,
      hEta, hPhysical, hUpper, hBlock⟩ := h415T
  refine ⟨W, etaAt, r, hr, W₁, hW₁, hSeparated, hCount, hCard,
    hEta, hPhysical, hUpper, ?_⟩
  by_cases hWEmpty : W₁ = ∅
  · exact Or.inl hWEmpty
  · right
    have hWNonempty : W₁.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWEmpty
    obtain ⟨u₀, hu₀⟩ := hWNonempty
    let U : ℕ := 2 ^ r * pintz2023SourceX T data.epsilon ell
    let baseI : Finset ℕ := pintz2023LocalizedInterval
      (pintz2023SourceX T data.epsilon ell)
      (pintz2023Cutoff (pintz2023SourceLambda T k)) r
    let R : ℝ := pintz2023CriticalScale k eta data.epsilon (2 * T)
    let V : ℝ :=
      (1 / (32 * Real.exp 2 *
          Real.log (pintz2023SourceLambda T k)) /
        pintz2023DyadicDepth
          (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2
    have hSupport := (hBlock u₀ hu₀).1
    have hXPos : 0 < pintz2023SourceX T data.epsilon ell := by
      apply pintz2023SourceX_pos
      exact Real.one_le_rpow hT.le (by
        exact div_nonneg data.epsilon_pos.le (by positivity))
    have hU : 0 < U := by
      dsimp only [U]
      exact Nat.mul_pos (pow_pos (by omega) _) hXPos
    have huLower : data.epsilon / (11 * (ell : ℝ)) <
        pintz2023LogScale T U := by
      simpa only [U] using hLowerT r
    have hSupport' : (U : ℝ) <
        (pintz2023SourceX T data.epsilon ell : ℝ) *
          (2 * T) ^
            pintz2023CriticalScaleExponent k eta data.epsilon := by
      simpa only [U, R, pintz2023CriticalScale] using hSupport
    have huUpperReserve : pintz2023LogScale T U <
        data.epsilon / (10 * (ell : ℝ)) +
          pintz2023CriticalScaleExponent k eta data.epsilon + data.delta := by
      exact pintz2023_logScale_upper_of_support hT hU hFactorT hSupport'
    have huUpper : pintz2023LogScale T U <
        pintz2023EllThreshold eta data.epsilon ell :=
      huUpperReserve.trans data.scale_separation
    obtain ⟨h, hhTwo, hhBound, hhLower, hhCase⟩ :=
      exists_pintz2023_power_choice hcell data.epsilon_pos
        data.epsilon_le_one data.power_smallness huLower huUpper
    have hh : 0 < h := lt_of_lt_of_le (by omega) hhTwo
    have hbaseI : baseI ⊆ Finset.Ioc U (2 * U) := by
      dsimp only [baseI, U]
      exact pintz2023LocalizedInterval_subset_dyadic _ _ _
    have hV : 0 ≤ V := by
      dsimp only [V]
      have hlog : 0 < Real.log (pintz2023SourceLambda T k) :=
        Real.log_pos hLambdaT
      positivity
    have hLarge : ∀ u ∈ W₁, V ≤
        ‖pintz2023SplitIntervalBlock
          (fun n => pintz2023SmallMCoeff
            (pintz2023SourceX T data.epsilon ell) n R)
          baseI
          ((((1 - etaAt u + 1 / pintz2023SourceLambda T k) : ℝ) : ℂ) +
            I * (u : ℂ))‖ := by
      intro u hu
      simpa only [V, R, baseI] using (hBlock u hu).2
    obtain ⟨q, hq, W₂, hW₂, hCard₂, hSecond⟩ :=
      exists_pintz2023_smallM_powered_block_and_subset
        (X := pintz2023SourceX T data.epsilon ell)
        (U := U) (h := h) (R := R) (V := V)
        (baseI := baseI) (W := W₁)
        (fun u => 1 - etaAt u + 1 / pintz2023SourceLambda T k)
        (fun u => u) hbaseI hU hh hV hLarge
    refine ⟨h, q, hq, W₂, hW₂, hSupport', hhTwo, hhBound,
      ?_, ?_, hCard₂, ?_⟩
    · simpa only [U] using hhLower
    · simpa only [U] using hhCase
    · intro u hu
      simpa only [U, R, V, baseI] using hSecond u hu

#print axioms eventually_exists_pintz2023_equation416_shell_family

end

end GafniTao
