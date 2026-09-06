import GafniTao.Pintz2023ShellLoss

/-!
# Pintz (2023), equation (4.24): one-shell epsilon exponent

This file combines the physical shell theorem, the exact detector-loss
ledger, and the two source scale alternatives.  The result is the genuine
multiplicity-weighted count on a dyadic height shell.
-/

open Asymptotics Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The exact equation-(4.24) epsilon-exponent estimate for one dyadic height
shell. -/
theorem pintz2023_dyadicHeightShell_epsilonExponentBound
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    EpsilonExponentBound
      (fun T => ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
        zeroMultiplicity rho : ℕ) : ℝ))
      (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell) := by
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hk : 0 < k := lt_of_lt_of_le (by omega) hcell.1
  obtain ⟨C, hC, hShell⟩ :=
    exists_eventually_pintz2023_equation419_shell_bound hcell data
  obtain ⟨Clog, hClog, hRemove⟩ :=
    exists_eventually_pintz2023_equation419_remove_threshold hcell data hC
  unfold EpsilonExponentBound EpsilonPowerBound
  intro eps heps
  have hQ : 0 < pintz2023ShellBlockExponent eta data.epsilon k :=
    pintz2023ShellBlockExponent_pos heta data.epsilon_pos hk
  let reserve : ℝ := eps / (2 * pintz2023ShellBlockExponent eta data.epsilon k)
  have hreserve : 0 < reserve := by
    dsimp only [reserve]
    positivity
  have hScale := eventually_pintz2023_equation416_powered_scale_split
    data hreserve
  have hLogSmall := eventually_const_mul_log_rpow_mul_negative_rpow_le
    (C := Clog) (p := pintz2023ShellLogExponent data) (q := eps / 2)
    (b := 1) hClog.le (half_pos heps) zero_lt_one
  apply IsBigO.of_bound 1
  filter_upwards [hShell, hRemove, hScale, hLogSmall,
    eventually_gt_atTop 1] with T hShellT hRemoveT hScaleT hLogSmallT hT
  have hTPos : 0 < T := zero_lt_one.trans hT
  have hTone : 1 ≤ T := hT.le
  have hlogPos : 0 < Real.log T := Real.log_pos hT
  have hLogBound :
      Clog * Real.log T ^ pintz2023ShellLogExponent data ≤ T ^ (eps / 2) := by
    have hpowPos : 0 < T ^ (eps / 2) := Real.rpow_pos_of_pos hTPos _
    have hcancel : T ^ (-eps / 2) * T ^ (eps / 2) = 1 := by
      rw [← Real.rpow_add hTPos]
      rw [show -eps / 2 + eps / 2 = 0 by ring, Real.rpow_zero]
    have hmul := mul_le_mul_of_nonneg_right hLogSmallT hpowPos.le
    calc
      Clog * Real.log T ^ pintz2023ShellLogExponent data =
          (Clog * Real.log T ^ pintz2023ShellLogExponent data *
            T ^ (-(eps / 2))) * T ^ (eps / 2) := by
        rw [show -(eps / 2) = -eps / 2 by ring]
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ 1 * T ^ (eps / 2) := hmul
      _ = T ^ (eps / 2) := one_mul _
  have hCountNonneg : 0 ≤
      ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
        zeroMultiplicity rho : ℕ) : ℝ) := by positivity
  have hCountPower :
      ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ) ≤
        T ^ (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell +
          eps) := by
    rcases hShellT with hZero | hWitness
    · rw [hZero]
      exact Real.rpow_nonneg hTPos.le _
    · obtain ⟨U, q, h, hU, hq, hhTwo, hhBound, hSupport,
          hhLower, hhCase, hRaw⟩ := hWitness
      let N : ℕ := 2 ^ q * U ^ h
      have hN : 0 < N := by
        dsimp only [N]
        exact Nat.mul_pos (pow_pos (by omega) q) (pow_pos hU h)
      have hhRange : h ∈ Finset.range (pintz2023ShellPowerCap data) := by
        unfold pintz2023ShellPowerCap
        rw [Finset.mem_range]
        have hCeil : 20 / data.epsilon ≤ (⌈20 / data.epsilon⌉₊ : ℝ) :=
          Nat.le_ceil _
        exact_mod_cast (show (h : ℝ) < ⌈20 / data.epsilon⌉₊ + 1 by
          exact hhBound.trans_le (by linarith))
      have hRemoved := hRemoveT hhRange
        (lt_of_lt_of_le (by omega) hhTwo) hN
        (((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ)) hCountNonneg
      have hCountN :
          ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
              zeroMultiplicity rho : ℕ) : ℝ) ≤
            Clog * Real.log T ^ pintz2023ShellLogExponent data *
              (N : ℝ) ^
                (2 * eta - 2 / pintz2023SourceLambda T k +
                  2 * (data.epsilon / (100 * (k : ℝ)))) := by
        exact hRemoved (by simpa only [N] using hRaw)
      have hLambdaPos : 0 < pintz2023SourceLambda T k :=
        pintz2023SourceLambda_pos hT hk
      have hpQ := pintz2023_equation419_exponent_le_blockExponent
        (eta := eta) (epsilon := data.epsilon) (k := k) hLambdaPos
      have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNExponent :
          (N : ℝ) ^
              (2 * eta - 2 / pintz2023SourceLambda T k +
                2 * (data.epsilon / (100 * (k : ℝ)))) ≤
            (N : ℝ) ^ pintz2023ShellBlockExponent eta data.epsilon k :=
        Real.rpow_le_rpow_of_exponent_le hNOne hpQ
      have hScaleSplit := hScaleT hU hq hhBound hSupport hhCase
      have hScaleDisjunction :
          ((N : ℝ) < T ^
              (pintz2023SquareBlockScale eta data.epsilon data.delta k ell +
                reserve)) ∨
          ((N : ℝ) < T ^
              (pintz2023EllPowerWindowUpper eta data.epsilon ell + reserve)) := by
        rcases hScaleSplit with hSquare | hEll
        · left
          simpa only [N, pintz2023SquareBlockScale] using hSquare.2
        · right
          simpa only [N] using hEll.2
      have hNScale := pintz2023_powered_block_rpow_le_shellCore
        heta data.epsilon_pos hk hTone hN hScaleDisjunction
      have hreserveCancel :
          pintz2023ShellBlockExponent eta data.epsilon k * reserve = eps / 2 := by
        dsimp only [reserve]
        field_simp [hQ.ne']
      rw [hreserveCancel] at hNScale
      calc
        _ ≤ Clog * Real.log T ^ pintz2023ShellLogExponent data *
              (N : ℝ) ^ pintz2023ShellBlockExponent eta data.epsilon k := by
          exact hCountN.trans (mul_le_mul_of_nonneg_left hNExponent
            (mul_nonneg hClog.le (Real.rpow_nonneg hlogPos.le _)))
        _ ≤ T ^ (eps / 2) *
              T ^ (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell +
                eps / 2) := by
          exact mul_le_mul hLogBound hNScale
            (Real.rpow_nonneg (by exact_mod_cast hN.le) _)
            (Real.rpow_nonneg hTPos.le _)
        _ = T ^ (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell +
              eps) := by
          rw [← Real.rpow_add hTPos]
          congr 1
          ring
  have hLeftNorm :
      ‖|((∑ rho ∈ pintz2023DyadicHeightShell eta T,
        zeroMultiplicity rho : ℕ) : ℝ)|‖ =
        ((∑ rho ∈ pintz2023DyadicHeightShell eta T,
          zeroMultiplicity rho : ℕ) : ℝ) := by
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hCountNonneg]
  have hRightNorm :
      ‖T ^ eps *
        |T ^ pintz2023ShellCoreExponent eta data.epsilon data.delta k ell|‖ =
        T ^ (pintz2023ShellCoreExponent eta data.epsilon data.delta k ell +
          eps) := by
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hTPos.le _), abs_abs,
      abs_of_nonneg (Real.rpow_nonneg hTPos.le _),
      ← Real.rpow_add hTPos]
    congr 1
    ring
  rw [hLeftNorm, one_mul, hRightNorm]
  exact hCountPower

#print axioms pintz2023_dyadicHeightShell_epsilonExponentBound

end

end GafniTao
