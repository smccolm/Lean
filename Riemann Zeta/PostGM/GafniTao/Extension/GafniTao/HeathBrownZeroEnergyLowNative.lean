import GafniTao.HeathBrownTunedGlobalLow

/-!
# Native low-range Heath--Brown zero-energy bounds

This file converts the genuine global bounded/source alternative into the
first two epsilon-exponent cells.  The auxiliary detector losses are sent to
zero inside the epsilon-power convention; no exponent-infimum attainment is
used.
-/

open Asymptotics Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- An eventual pointwise domination between nonnegative functions transfers
an epsilon-exponent estimate. -/
theorem EpsilonExponentBound.mono_eventually_nonneg
    {f g : Real -> Real} {a : Real}
    (hf : ∀ᶠ T in atTop, 0 <= f T)
    (hg : ∀ᶠ T in atTop, 0 <= g T)
    (hfg : ∀ᶠ T in atTop, f T <= g T)
    (hga : EpsilonExponentBound g a) :
    EpsilonExponentBound f a := by
  unfold EpsilonExponentBound EpsilonPowerBound at hga ⊢
  intro eps heps
  have hdom : (fun T => |f T|) =O[atTop] (fun T => |g T|) := by
    apply IsBigO.of_bound 1
    filter_upwards [hf, hg, hfg] with T hfT hgT hfgT
    simpa only [Real.norm_eq_abs, abs_abs, one_mul,
      abs_of_nonneg hfT, abs_of_nonneg hgT] using hfgT
  exact hdom.trans (hga eps heps)

/-- If every positive enlargement of an exponent is available, the central
exponent is available under the epsilon-power convention. -/
theorem epsilonExponentBound_of_all_positive_margin
    {f : Real -> Real} {a : Real}
    (h : forall d : Real, 0 < d -> EpsilonExponentBound f (a + d)) :
    EpsilonExponentBound f a := by
  unfold EpsilonExponentBound EpsilonPowerBound at h ⊢
  intro eps heps
  have H := h (eps / 2) (by positivity) (eps / 2) (by positivity)
  apply H.trans_eventuallyEq
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  rw [abs_of_nonneg (Real.rpow_nonneg hT.le _),
    abs_of_nonneg (Real.rpow_nonneg hT.le _),
    ← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  ring

/-- The exact fourth-power dyadic source contribution has the requested low
cell exponent after spending the strict detector margin. -/
theorem heathBrown_low_source_term_margin
    {L d : Real} (hd : 0 < d) :
    EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 *
        T ^ (L + 2 * d / 3))
      (L + d) := by
  have hPower : EpsilonExponentBound
      (fun T : Real => T ^ (L + 2 * d / 3))
      (L + 2 * d / 3) := by
    exact EpsilonPowerBound.refl _
  exact hPower.dyadic_shell_four_loss |>.mono_exponent (by linarith)

/-- Global low-range energy bound before selecting the first or second
closed cell.  This consumes the actual global shell cover and all four source
colors through `exists_eventual_heathBrown_tuned_global_low_majorant`. -/
theorem heathBrown_zeroAdditiveEnergy_low_max_native
    {sigma : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    EpsilonExponentBound
      (fun T => (zeroAdditiveEnergyCount sigma T : Real))
      (max (heathBrownLowFirstSlope sigma)
        (heathBrownLowSecondSlope sigma)) := by
  let L := max (heathBrownLowFirstSlope sigma)
    (heathBrownLowSecondSlope sigma)
  apply epsilonExponentBound_of_all_positive_margin
  intro d hd
  obtain ⟨R, T0, _hR, _hT0, hPoint⟩ :=
    exists_eventual_heathBrown_tuned_global_low_majorant
      hsigma hsigmaUpper hd
  have hBounded : EpsilonExponentBound
      (fun T => (dyadicZeroShellCount T : Real) ^ 4 *
        heathBrownBoundedShellMajorant sigma R T) L := by
    by_cases hfirst : sigma <= 2 / 3
    · have h := heathBrownGlobalBoundedMajorant_first_cell
        (R0 := R) hsigma.le hfirst
      have hCancel :
          ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) *
              (1 - sigma) = heathBrownLowFirstSlope sigma := by
        unfold heathBrownLowFirstSlope
        have hne : 1 - sigma ≠ 0 := by linarith
        field_simp [hne]
      simpa only [L, heathBrown_low_max_eq_first hfirst, hCancel] using h
    · have hsecond : 2 / 3 <= sigma := by linarith
      have h := heathBrownGlobalBoundedMajorant_second_cell
        (R0 := R) hsecond hsigmaUpper
      have hCancel :
          ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) *
              (1 - sigma) = heathBrownLowSecondSlope sigma := by
        unfold heathBrownLowSecondSlope
        have hne : 1 - sigma ≠ 0 := by linarith
        field_simp [hne]
      simpa only [L,
        heathBrown_low_max_eq_second hsecond hsigmaUpper, hCancel] using h
  have hBoundedMargin := hBounded.mono_exponent
    (show L <= L + d by linarith)
  have hSourceMargin := heathBrown_low_source_term_margin
    (L := L) hd
  have hSum : EpsilonExponentBound
      (fun T =>
        (dyadicZeroShellCount T : Real) ^ 4 *
            heathBrownBoundedShellMajorant sigma R T +
          (dyadicZeroShellCount T : Real) ^ 4 *
            T ^ (L + 2 * d / 3))
      (L + d) := hBoundedMargin.add hSourceMargin
  apply hSum.mono_eventually_nonneg
  · exact Filter.Eventually.of_forall fun _ => by positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 2)] with T hT
    have hTOne : 1 <= T := by
      have : 1 <= Real.exp 2 := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (by norm_num : (0 : Real) <= 2))
      exact this.trans hT
    have hLog : 0 <= Real.log (2 * (Nat.ceil T : Real)) :=
      Real.log_nonneg (by
        have hCeil : 1 <= (Nat.ceil T : Real) := hTOne.trans (Nat.le_ceil T)
        linarith)
    have hBoundedNonneg :
        0 <= heathBrownBoundedShellMajorant sigma R T := by
      unfold heathBrownBoundedShellMajorant
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le) hLog)
    positivity
  · filter_upwards [eventually_ge_atTop T0,
      eventually_ge_atTop (Real.exp 2)] with T hT hTExp
    have hTOne : 1 <= T := by
      have : 1 <= Real.exp 2 := by
        simpa only [Real.exp_zero] using
          (Real.exp_le_exp.mpr (by norm_num : (0 : Real) <= 2))
      exact this.trans hTExp
    have hLog : 0 <= Real.log (2 * (Nat.ceil T : Real)) :=
      Real.log_nonneg (by
        have hCeil : 1 <= (Nat.ceil T : Real) := hTOne.trans (Nat.le_ceil T)
        linarith)
    have hBoundedNonneg :
        0 <= heathBrownBoundedShellMajorant sigma R T := by
      unfold heathBrownBoundedShellMajorant
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (mul_nonneg
          (mul_nonneg (by norm_num) globalLocalZeroLogConstant_pos.le) hLog)
    have hPowerNonneg : 0 <= T ^ (L + 2 * d / 3) := by positivity
    calc
      (zeroAdditiveEnergyCount sigma T : Real) <=
          (dyadicZeroShellCount T : Real) ^ 4 *
            max (heathBrownBoundedShellMajorant sigma R T)
              (T ^ (L + 2 * d / 3)) := by
        simpa only [L] using hPoint T hT
      _ <= (dyadicZeroShellCount T : Real) ^ 4 *
            heathBrownBoundedShellMajorant sigma R T +
          (dyadicZeroShellCount T : Real) ^ 4 *
            T ^ (L + 2 * d / 3) := by
        have hmax : max (heathBrownBoundedShellMajorant sigma R T)
            (T ^ (L + 2 * d / 3)) <=
              heathBrownBoundedShellMajorant sigma R T +
                T ^ (L + 2 * d / 3) :=
          max_le (le_add_of_nonneg_right hPowerNonneg)
            (le_add_of_nonneg_left hBoundedNonneg)
        calc
          (dyadicZeroShellCount T : Real) ^ 4 *
              max (heathBrownBoundedShellMajorant sigma R T)
                (T ^ (L + 2 * d / 3)) <=
            (dyadicZeroShellCount T : Real) ^ 4 *
              (heathBrownBoundedShellMajorant sigma R T +
                T ^ (L + 2 * d / 3)) :=
                  mul_le_mul_of_nonneg_left hmax (by positivity)
          _ = _ := by ring

/-- First Heath--Brown cell away from the left endpoint. -/
theorem heathBrown_zeroAdditiveEnergy_first_open_native
    {sigma : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 2 / 3) :
    ZeroAdditiveEnergyEnvelope sigma
      ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) := by
  unfold ZeroAdditiveEnergyEnvelope
  have h := heathBrown_zeroAdditiveEnergy_low_max_native hsigma
    (hsigmaUpper.trans (by norm_num : (2 / 3 : Real) <= 3 / 4))
  rw [heathBrown_low_max_eq_first hsigmaUpper] at h
  have hCancel :
      ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) *
          (1 - sigma) = heathBrownLowFirstSlope sigma := by
    unfold heathBrownLowFirstSlope
    have hne : 1 - sigma ≠ 0 := by linarith
    field_simp [hne]
  rw [hCancel]
  exact h

/-- Second Heath--Brown cell with the source's open lower endpoint. -/
theorem heathBrown_zeroAdditiveEnergy_second_native
    {sigma : Real} (hsigmaLower : 2 / 3 < sigma)
    (hsigmaUpper : sigma <= 3 / 4) :
    ZeroAdditiveEnergyEnvelope sigma
      ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) := by
  unfold ZeroAdditiveEnergyEnvelope
  have h := heathBrown_zeroAdditiveEnergy_low_max_native
    (show 1 / 2 < sigma by linarith) hsigmaUpper
  rw [heathBrown_low_max_eq_second hsigmaLower.le hsigmaUpper] at h
  have hCancel :
      ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) *
          (1 - sigma) = heathBrownLowSecondSlope sigma := by
    unfold heathBrownLowSecondSlope
    have hne : 1 - sigma ≠ 0 := by linarith
    field_simp [hne]
  rw [hCancel]
  exact h

/-- The left endpoint follows from the unit-local-zero bound and the
publication-facing Ingham density theorem; it is not obtained by a continuity
claim about the exponent infimum. -/
theorem heathBrown_zeroAdditiveEnergy_first_left_endpoint_native :
    ZeroAdditiveEnergyEnvelope (1 / 2)
      ((10 - 11 * (1 / 2 : Real)) /
        ((2 - 1 / 2) * (1 - 1 / 2))) := by
  have hDensity := ingham_zeroDensityEnvelope
    (show (1 / 2 : Real) <= 1 / 2 by rfl)
    (show (1 / 2 : Real) <= 1 by norm_num)
  have hEnergy := zeroAdditiveEnergyEnvelope_three_mul_of_zeroDensityEnvelope
    (show (0 : Real) <= 1 / 2 by norm_num) hDensity
  norm_num at hEnergy ⊢
  exact hEnergy

/-- Complete first Heath--Brown cell, including `sigma=1/2`. -/
theorem heathBrown_zeroAdditiveEnergy_first_native
    {sigma : Real} (hsigmaLower : 1 / 2 <= sigma)
    (hsigmaUpper : sigma <= 2 / 3) :
    ZeroAdditiveEnergyEnvelope sigma
      ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) := by
  rcases hsigmaLower.eq_or_lt with rfl | hsigma
  · exact heathBrown_zeroAdditiveEnergy_first_left_endpoint_native
  · exact heathBrown_zeroAdditiveEnergy_first_open_native hsigma hsigmaUpper

#print axioms EpsilonExponentBound.mono_eventually_nonneg
#print axioms epsilonExponentBound_of_all_positive_margin
#print axioms heathBrown_zeroAdditiveEnergy_low_max_native
#print axioms heathBrown_zeroAdditiveEnergy_first_native
#print axioms heathBrown_zeroAdditiveEnergy_second_native

end

end GafniTao
