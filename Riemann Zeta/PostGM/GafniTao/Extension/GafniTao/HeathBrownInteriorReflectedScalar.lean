import GafniTao.HeathBrownInteriorReflectedEnergy

/-!
# Scalar data for every reflected Type-I dyadic family

The frozen endpoint theorem selects one dyadic family by cardinality.  Such a
selection does not preserve four-fold additive energy.  This file separates
the scalar part of that argument: every nonempty dyadic family produced by
the energy-safe four-coordinate extraction satisfies the same scale and
threshold estimates.  No family is selected here.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Every nonempty reflected dyadic block has the physical scale and literal
threshold bounds used in the Heath--Brown power argument. -/
theorem eventually_interior_reflected_dyadic_scalar_data
    {sigma d u : Real} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (huD : u ≤ d) :
    ∃ Clog : Real, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ T₀ : Real, 8 ≤ T₀ ∧
        ∀ {T tau : Real} {Y A r : Nat}, T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 →
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat)
          let Rdet := (Real.pi * V) /
            (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := Rdet / (2 * (M : Real) ^ sigma)
          let L := S / Nat.clog 2 M
          ∀ (j : Fin (Nat.clog 2 M)) (U : Finset Real),
            U.Nonempty →
            (∀ n ∈ dyadicInterval (2 ^ (j : Nat)),
              ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1) →
            (∀ t ∈ U, L ≤
              ‖dirichletPoly (2 ^ (j : Nat))
                (normalizedTypeIReflectedCoeff sigma M) t‖) →
            1 < 2 ^ (j : Nat) ∧ 2 ^ (j : Nat) < M ∧
              1 / (1 / 2 + d) ≤
                typeILogarithmicScale T (2 ^ (j : Nat)) ∧
              typeILogarithmicScale T (2 ^ (j : Nat)) ≤ Uscale ∧
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
                  Cref ≤ L ∧
              T ^ g / Cref ≤ L := by
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let CK : Real := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  have hCK : 0 < CK := by dsimp only [CK]; positivity
  let Cref : Real := mediumReflectedThresholdConstant Clog CK
  have hCref : 1 ≤ Cref := by
    dsimp only [Cref, mediumReflectedThresholdConstant]
    exact le_max_left _ _
  let g : Real := (sigma - 1 / 2) / 2
  have hg : 0 < g := by dsimp only [g]; linarith
  let Uscale : Real := 2 / g
  have hUscale : 0 < Uscale := by dsimp only [Uscale]; positivity
  obtain ⟨Tscale, hTscale, hScaleUpper⟩ :=
    eventually_threshold_forces_logarithmic_scale_upper hg hCref
  let T₀ : Real := max Tlog Tscale
  refine ⟨Clog, hClog, hCref, hg, hUscale, T₀,
    hTlog.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r hT hA hY hr hUpper hTau hTauOne hTauTwo
  dsimp only
  intro j U hUNonempty hCoeff hLarge
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTEight : 8 ≤ T := hTlog.trans hTLog
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Q : Nat := 2 ^ r * Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have : 4 ≤ Q := by
      dsimp only [Q]
      exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : Real) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  let M : Nat := mediumTypeIDualCutoff T d Q
  let V : Real := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : Nat)
  let Rdet : Real := (Real.pi * V) /
    (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : Real := Rdet / (2 * (M : Real) ^ sigma)
  let L : Real := S / Nat.clog 2 M
  have hClogM : 0 < Nat.clog 2 M := Nat.zero_lt_of_lt j.isLt
  have hM : 1 < M := by
    by_contra hnot
    have hMOne : M ≤ 1 := by omega
    have hClogZero : Nat.clog 2 M ≤ 0 := by
      apply Nat.clog_le_of_le_pow
      simpa using hMOne
    omega
  have hL : 0 < L := by
    dsimp only [L, S, Rdet, V]
    have hKernelPos := mediumTypeIStationaryKernel_pos
      (sigma := sigma) hTPos (lt_trans Nat.zero_lt_one hQOne)
    have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    positivity
  have hLogsAt := hLogs T hTLog
  have hLogProduct := medium_reflected_clog_product_le hTEight hd.le
    (by nlinarith [hdGap, hsigmaUpper] : d ≤ 1 / 2) hQOne
      (by linarith) hTauTwo hScale
  have hLogsM :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : Nat) : Real) *
          (Nat.clog 2 M : Real) ≤ Clog * T ^ d := by
    simpa only [M] using hLogProduct.trans hLogsAt
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Q) hTPos.le
  have hQEq : (Q : Real) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQOne (by linarith) hScale
  have hMUpper : (M : Real) ≤ T ^ (1 + d - 1 / tau) := by
    calc
      (M : Real) ≤ T ^ (1 + d) / Q := by
        simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQEq, ← Real.rpow_sub hTPos]
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQOne hTauOne hTauTwo hScale
  have hThresholdRaw := medium_reflected_threshold_explicit_lower
    (sigma := sigma) (T := T) (tau := tau) (d := d) (u := u)
    (eta := d) (Clog := Clog) (CK := CK) (Q := Q) (M := M)
    (by linarith) hTOne hQOne hM (by linarith) hScale hMUpper hClog
    hLogsM hCK (by simpa only [CK] using hKernel)
  have hThresholdExact :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
          Cref ≤ L := by
    simpa only [Cref, L, S, Rdet, V, Q, M, hA] using hThresholdRaw
  have hExponent := medium_reflected_threshold_exponent_lower hsigma
    hsigmaUpper hTauOne hd hdGap huD
  have hThreshold : T ^ g / Cref ≤ L := by
    have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hExponent
    exact (div_le_div_of_nonneg_right hPow
      (zero_le_one.trans hCref)).trans (by
        simpa only [g, Cref, L, S, Rdet, V, Q, M, hA] using hThresholdRaw)
  have hLToP : L ≤ ((2 ^ (j : Nat) : Nat) : Real) :=
    unit_coeff_threshold_le_dyadic_length hL.le hUNonempty hCoeff hLarge
  have hScaleData := hScaleUpper hTScale hL hThreshold hLToP
  rcases hScaleData with ⟨hPOne, hTauPUpper⟩
  have hPLtM : 2 ^ (j : Nat) < M :=
    Nat.pow_lt_of_lt_clog j.isLt
  have hTauPLower := reflected_dyadic_scale_lower_of_expanded_cutoff
    (T := T) (τ := tau) (d := d) (Q := Q) (P := 2 ^ (j : Nat)) (M := M)
    (by linarith) hQOne hPOne hTauOne hTauTwo hd.le hScale hPLtM.le
      (by simpa only [M] using hMUpperRaw)
  exact ⟨hPOne, hPLtM, hTauPLower,
    by simpa only [Uscale] using hTauPUpper,
    by simpa only [L, S, Rdet, V, Q, M] using hThresholdExact,
    by simpa only [g, Cref, L, S, Rdet, V, Q, M] using hThreshold⟩

#print axioms eventually_interior_reflected_dyadic_scalar_data

end

end GafniTao
