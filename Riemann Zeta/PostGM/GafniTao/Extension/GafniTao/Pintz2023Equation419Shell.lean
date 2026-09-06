import GafniTao.Pintz2023Equation416
import GafniTao.Pintz2023Equation419UniformConstant
import GafniTao.Pintz2023PoweredScaleLower
import GafniTao.Pintz2023PoweredScaleUpper
import GafniTao.Pintz2023SignLocalization

/-!
# Pintz (2023), equation (4.19): physical shell assembly

This file consumes the actual alternatives returned by equation (4.16).
The nonempty branch keeps the selected source block and power, performs the
same-sign localization, and applies the uniform equation-(4.19) theorem. One
analytic constant is chosen before the height and the power; every remaining
selection and logarithmic loss is displayed for the final exponent argument.
-/

open Complex Finset Filter
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Source-facing multiplicity estimate on one dyadic height shell. The
constant is uniform in the physical height and in the power selected by
equation (4.16). -/
theorem exists_eventually_pintz2023_equation419_shell_bound
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ) = 0 ∨
      ∃ U q h : ℕ,
        0 < U ∧ q < h ∧ 2 ≤ h ∧ (h : ℝ) < 20 / data.epsilon ∧
        (U : ℝ) <
          (pintz2023SourceX T data.epsilon ell : ℝ) *
            (2 * T) ^
              pintz2023CriticalScaleExponent k eta data.epsilon ∧
        pintz2023EllThreshold eta data.epsilon ell <
          (h : ℝ) * pintz2023LogScale T U ∧
        (h = 2 ∨
          (h : ℝ) * pintz2023LogScale T U <
            pintz2023EllPowerWindowUpper eta data.epsilon ell) ∧
        let N : ℕ := 2 ^ q * U ^ h
        let A : ℝ :=
          ((1 / (32 * Real.exp 2 *
                Real.log (pintz2023SourceLambda T k)) /
              pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
        let epsilonCoeff := data.epsilon / (100 * (k : ℝ))
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho : ℕ) : ℝ) * A ^ 2 ≤
          ((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) *
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
            (h : ℝ) * 2 * C *
            (N : ℝ) ^
              (2 * eta - 2 / pintz2023SourceLambda T k +
                2 * epsilonCoeff) := by
  have h416 := eventually_exists_pintz2023_equation416_shell_family
    hcell data
  obtain ⟨C, hC, hUniform⟩ :=
    exists_eventually_forall_pintz2023_equation419_normalized_at hcell data
  have hUpper := eventually_pintz2023_source_powered_block_lt_cube
    hcell data
  refine ⟨C, hC, ?_⟩
  filter_upwards [h416, hUniform, hUpper,
    eventually_eight_mul_log_le_identity,
    eventually_gt_atTop 1] with T h416T hUniformT hUpperT hLogT hT
  obtain ⟨W, etaAt, r, hr, W₁, hW₁, hSeparated, hCount, hCard,
      hEta, hPhysical, hPhysicalUpper, hBranch⟩ := h416T
  rcases hBranch with hEmpty | hNonempty
  · left
    have hW₁card : W₁.card = 0 := Finset.card_eq_zero.mpr hEmpty
    have hWcard : W.card = 0 := by
      have hWcardReal : (W.card : ℝ) ≤ 0 := by
        simpa [hW₁card] using hCard
      exact_mod_cast le_antisymm hWcardReal (Nat.cast_nonneg W.card)
    have hCountZero :
        ∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho = 0 := by
      simpa [hWcard] using hCount
    exact_mod_cast hCountZero
  · right
    obtain ⟨h, q, hq, W₂, hW₂, hSupport, hhTwo, hhBound,
      hhLower, hhCase, hCard₂, hDetected⟩ := hNonempty
    let U : ℕ := 2 ^ r * pintz2023SourceX T data.epsilon ell
    let N : ℕ := 2 ^ q * U ^ h
    let R : ℝ := pintz2023CriticalScale k eta data.epsilon (2 * T)
    let baseI : Finset ℕ := pintz2023LocalizedInterval
      (pintz2023SourceX T data.epsilon ell)
      (pintz2023Cutoff (pintz2023SourceLambda T k)) r
    let A : ℝ :=
      ((1 / (32 * Real.exp 2 *
            Real.log (pintz2023SourceLambda T k)) /
          pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k))) / 2) ^ h / h
    have hSourceX : 0 < pintz2023SourceX T data.epsilon ell := by
      apply pintz2023SourceX_pos
      exact Real.one_le_rpow hT.le
        (div_nonneg data.epsilon_pos.le (by positivity))
    have hU : 0 < U := by
      dsimp only [U]
      exact Nat.mul_pos (pow_pos (by omega) r) hSourceX
    have hN : 0 < N := by
      dsimp only [N]
      exact Nat.mul_pos (pow_pos (by omega) q) (pow_pos hU h)
    have hCriticalStrict :
        T ^ pintz2023EllThreshold eta data.epsilon ell < (N : ℝ) :=
      pintz2023_equation416_critical_scale_lt hT hU hhLower
    have hNCube : (N : ℝ) ≤ T ^ (3 : ℝ) :=
      (hUpperT hU (Finset.mem_range.mp hq) hhBound hSupport hhCase).le
    have hLambdaUpper : 2 * pintz2023SourceLambda T k ≤ T / 4 := by
      unfold pintz2023SourceLambda
      have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hcell.1
      have hratio : 2 / (k : ℝ) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith)
      have hlogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT.le
      have hLambdaLog : pintz2023SourceLambda T k ≤ Real.log T := by
        unfold pintz2023SourceLambda
        nlinarith [mul_le_mul_of_nonneg_right hratio hlogNonneg]
      nlinarith
    obtain ⟨Z, hZ, hCardZ, hDifference⟩ :=
      exists_pintz2023_sameSign_subfamily
        (fun u hu => hPhysical u (hW₂ hu))
        (fun u hu => hPhysicalUpper u (hW₂ hu)) hLambdaUpper
    have hhRange : h ∈ Finset.range (⌈20 / data.epsilon⌉₊ + 1) := by
      rw [Finset.mem_range]
      have hCeil : 20 / data.epsilon ≤ (⌈20 / data.epsilon⌉₊ : ℝ) :=
        Nat.le_ceil _
      exact_mod_cast (show (h : ℝ) < ⌈20 / data.epsilon⌉₊ + 1 by
        exact hhBound.trans_le (by linarith))
    obtain ⟨N₀, hN₀Scale, hHalasz⟩ :=
      hUniformT h hhRange (lt_of_lt_of_le (by omega) hhTwo)
    have hN₀ : N₀ ≤ N := by
      have hN₀Real : (N₀ : ℝ) ≤ (N : ℝ) :=
        hN₀Scale.trans hCriticalStrict.le
      exact_mod_cast hN₀Real
    have hbaseI : baseI ⊆ Finset.Ioc U (2 * U) := by
      dsimp only [baseI, U]
      exact pintz2023LocalizedInterval_subset_dyadic _ _ _
    have hSepZ : IsSeparated (3 * pintz2023SourceLambda T k) Z := by
      intro u hu v hv huv
      exact hSeparated u (hW₁ (hW₂ (hZ hu)))
        v (hW₁ (hW₂ (hZ hv))) huv
    have hEtaZ : ∀ u ∈ Z, etaAt u ∈ Set.Icc 0 eta := by
      intro u hu
      exact hEta u (hW₂ (hZ hu))
    have hDetectedZ : ∀ u ∈ Z,
        A ≤ ‖dirichletPoly N
          (pintz2023SmallMPoweredLineCoeff
            (pintz2023SourceX T data.epsilon ell) R baseI h
            (1 - etaAt u + 1 / pintz2023SourceLambda T k)) u‖ := by
      intro u hu
      simpa only [A, N, R, baseI, U] using hDetected u (hZ hu)
    have hHZ := hHalasz
      (pintz2023SourceX T data.epsilon ell) U N R baseI Z etaAt
      hbaseI hU hN hN₀ hT.le hCriticalStrict.le hNCube hSepZ hEtaZ
      hDifference hDetectedZ
    let epsilonCoeff : ℝ := data.epsilon / (100 * (k : ℝ))
    have hHZ' : (Z.card : ℝ) * A ^ 2 ≤
        C * (N : ℝ) ^
          (2 * eta - 2 / pintz2023SourceLambda T k +
            2 * epsilonCoeff) := by
      simpa only [A, epsilonCoeff] using hHZ
    have hCountReal :
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho : ℕ) : ℝ) ≤
          ((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) *
            (W.card : ℝ) := by
      exact_mod_cast hCount
    have hCardChain : (W.card : ℝ) ≤
        pintz2023DyadicDepth
            (pintz2023Cutoff (pintz2023SourceLambda T k)) *
          (h : ℝ) * 2 * (Z.card : ℝ) := by
      calc
        (W.card : ℝ) ≤
            pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
                (W₁.card : ℝ) := hCard
        _ ≤ pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
                ((h : ℝ) * (W₂.card : ℝ)) := by gcongr
        _ ≤ pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) *
                ((h : ℝ) * (2 * (Z.card : ℝ))) := by gcongr
        _ = _ := by ring
    have hLossNonneg : 0 ≤
        (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
            (2 * (2 * Nat.ceil
              (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) := by
      positivity
    have hCountToZ :
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
            zeroMultiplicity rho : ℕ) : ℝ) ≤
          ((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) *
            (pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k)) *
              (h : ℝ) * 2 * (Z.card : ℝ)) :=
      hCountReal.trans (mul_le_mul_of_nonneg_left hCardChain hLossNonneg)
    have hMultiply := mul_le_mul_of_nonneg_right hCountToZ (sq_nonneg A)
    have hFactorNonneg : 0 ≤
        (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) *
          (pintz2023DyadicDepth
              (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) *
          (h : ℝ) * 2 := by
      positivity
    have hUseHZ := mul_le_mul_of_nonneg_left hHZ' hFactorNonneg
    refine ⟨U, q, h, hU, Finset.mem_range.mp hq, hhTwo, hhBound,
      hSupport, hhLower, hhCase, ?_⟩
    dsimp only [N, A, epsilonCoeff]
    calc
      _ ≤
          (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) *
            (pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k)) *
              (h : ℝ) * 2 * (Z.card : ℝ)) * A ^ 2 := hMultiply
      _ =
          (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) *
            (pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) *
            (h : ℝ) * 2 * ((Z.card : ℝ) * A ^ 2) := by ring
      _ ≤
          (((2 * Nat.ceil (globalLocalZeroLogConstant * Real.log T)) *
              (2 * (2 * Nat.ceil
                (7 * pintz2023SourceLambda T k) + 1)) : ℕ) : ℝ) *
            (pintz2023DyadicDepth
                (pintz2023Cutoff (pintz2023SourceLambda T k)) : ℝ) *
            (h : ℝ) * 2 *
              (C * (N : ℝ) ^
                (2 * eta - 2 / pintz2023SourceLambda T k +
                  2 * epsilonCoeff)) := hUseHZ
      _ = _ := by ring

#print axioms exists_eventually_pintz2023_equation419_shell_bound

end

end GafniTao
