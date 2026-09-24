import TaoTrudgianYang2025.ClassicalReflectedCardinality

/-!
# Actual source reflection with positive separated ordinates

The native Poisson, kernel and tail estimates are assembled before
extracting the literal reflected coefficient block. Its physical scale,
threshold and cardinality loss stay linked to the original source family.
This is an analytic reflection factory, not yet the endpoint-two zeta-LV
cardinality consumer.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_interior_source_positive_reflected_data
    {sigma d u : ℝ} (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma < 1) (hd : 0 < d) (hdOne : d ≤ 1)
    (hdGap : d ≤ (sigma - 1 / 2) / 1000)
    (hu : 0 ≤ u) (huD : u ≤ d) :
    ∃ Clog : ℝ, 0 < Clog ∧
      let CK := 32 * 2 ^ sigma +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          4 ^ (sigma + 1 / 2)
      let Cref := mediumReflectedThresholdConstant Clog CK
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      1 ≤ Cref ∧ 0 < g ∧ 0 < Uscale ∧
      ∃ T₀ : ℝ, 8 ≤ T₀ ∧
        ∀ {T tau : ℝ} {Y A r : ℕ} (W : Finset ℝ), T₀ ≤ T →
          A = ⌊sharpZetaCutoff T⌋₊ → 0 < Y → 2 ≤ r →
          ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2) →
          2 * (2 ^ r * Y) ≤ A →
          tau = typeILogarithmicScale T (2 ^ r * Y) →
          1 < tau → tau < 2 →
          W.Nonempty → IsSeparated 1 W →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-u) / 2)) /
                (Nat.clog 2 A + 1 : ℕ) ≤
              ‖typeISourceSmoothBlock Y A r sigma t‖) →
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : ℕ)
          let R := (Real.pi * V) /
            (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := R / (2 * (M : ℝ) ^ sigma)
          let L := S / Nat.clog 2 M
          ∃ j ∈ Finset.range (Nat.clog 2 M), ∃ U : Finset ℝ,
              IsSeparated 1 U ∧
              (∀ v ∈ U, T / 2 ≤ v ∧ v ≤ 5 * T / 2) ∧
              W.card ≤ 2 * (2 * (2 * ⌈T ^ d⌉₊ + 1)) *
                (Nat.clog 2 M) * U.card ∧
              (∀ n ∈ dyadicInterval (2 ^ j),
                ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1) ∧
              (∀ v ∈ U, L ≤ ‖dirichletPoly (2 ^ j)
                (normalizedTypeIReflectedCoeff sigma M) v‖) ∧
              1 < 2 ^ j ∧ 2 ^ j < M ∧
              1 / (1 / 2 + d) ≤ typeILogarithmicScale T (2 ^ j) ∧
              typeILogarithmicScale T (2 ^ j) ≤ Uscale ∧
              T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
                  Cref ≤ L ∧
              T ^ g / Cref ≤ L := by
  obtain ⟨Clog, hClog, Tlog, hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le d hd
  let CK : ℝ := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  have hCK : 0 < CK := by dsimp only [CK]; positivity
  let Cref : ℝ := mediumReflectedThresholdConstant Clog CK
  have hCref : 1 ≤ Cref := by
    dsimp only [Cref, mediumReflectedThresholdConstant]
    exact le_max_left _ _
  let g : ℝ := (sigma - 1 / 2) / 2
  have hg : 0 < g := by dsimp only [g]; linarith
  let Uscale : ℝ := 2 / g
  have hUscale : 0 < Uscale := by dsimp only [Uscale]; positivity
  obtain ⟨Treflect, hTreflect, hReflect⟩ :=
    eventually_interior_source_family_reflects hsigma hsigmaUpper hd hdOne
      hdGap hu huD
  obtain ⟨Tscale, hTscale, hScaleUpper⟩ :=
    eventually_threshold_forces_logarithmic_scale_upper hg hCref
  have hdStrict : d < 1 := by nlinarith [hdGap]
  obtain ⟨Twindow, hTwindow, hWindow⟩ :=
    eventually_two_mul_rpow_le_half_sub_two hd hdStrict
  let T₀ : ℝ := max Tlog (max Treflect (max Tscale Twindow))
  refine ⟨Clog, hClog, hCref, hg, hUscale, T₀,
    hTlog.trans (le_max_left _ _), ?_⟩
  intro T tau Y A r W hT hA hY hr hLower hUpper hTau htauOne htauTwo
    hW hSep hRange hLarge
  dsimp only
  have hTLog : Tlog ≤ T := (le_max_left _ _).trans hT
  have hRest : max Treflect (max Tscale Twindow) ≤ T :=
    (le_max_right _ _).trans hT
  have hTReflect : Treflect ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tscale Twindow ≤ T := (le_max_right _ _).trans hRest
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest₁
  have hTWindow : Twindow ≤ T := (le_max_right _ _).trans hRest₁
  have hTEight : 8 ≤ T := hTlog.trans hTLog
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  let Q : ℕ := 2 ^ r * Y
  have hQOne : 1 < Q := by
    have hPow : 4 ≤ 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have : 4 ≤ Q := by
      dsimp only [Q]
      exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScale : (Q : ℝ) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hReflected := hReflect (T := T) (tau := tau) (Y := Y) (A := A)
    (r := r) W hTReflect hA hY hr hLower hUpper hTau htauOne htauTwo
      hRange hLarge hW
  let M : ℕ := mediumTypeIDualCutoff T d Q
  rcases hReflected with ⟨hMOne, hEach⟩
  have hDH : T ^ d + T ^ d ≤ T / 2 := by
    have := hWindow T hTWindow
    nlinarith
  have hExtract := extract_positive_ordinate_reflected_block W hMOne
    (Real.rpow_nonneg hTPos.le d) hTPos.le hDH hSep hRange hEach
  obtain ⟨j, hj, U, hSepU, hURange, hCardU, hLargeU⟩ := hExtract
  have hCoeff : ∀ n ∈ dyadicInterval (2 ^ j),
      ‖normalizedTypeIReflectedCoeff sigma M n‖ ≤ 1 := by
    intro n _
    exact norm_normalizedTypeIReflectedCoeff_le_one (by linarith)
      (lt_trans Nat.zero_lt_one hMOne)
  let V : ℝ := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : ℕ)
  let R : ℝ := (Real.pi * V) /
    (8 * (Q : ℝ) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : ℝ := R / (2 * (M : ℝ) ^ sigma)
  let L : ℝ := S / Nat.clog 2 M
  have hMOne' : 1 < M := by simpa only [M, Q] using hMOne
  have hClogM : 0 < Nat.clog 2 M :=
    Nat.clog_pos Nat.one_lt_two hMOne'
  have hL : 0 < L := by
    dsimp only [L, S, R, V]
    have hKernelPos := mediumTypeIStationaryKernel_pos (sigma := sigma) hTPos
      (lt_trans Nat.zero_lt_one hQOne)
    have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
      linarith [typeIDyadicCutoffMellinL1_nonneg]
    positivity
  have hLogsAt := hLogs T hTLog
  have hLogProduct := medium_reflected_clog_product_le hTEight hd.le
    (by nlinarith [hdGap, hsigmaUpper] : d ≤ 1 / 2) hQOne (by linarith)
      htauTwo hScale
  have hLogsM :
      ((Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ + 1 : ℕ) : ℝ) *
          (Nat.clog 2 M : ℝ) ≤ Clog * T ^ d := by
    simpa only [M] using hLogProduct.trans hLogsAt
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Q) hTPos.le
  have hQEq : (Q : ℝ) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQOne (by linarith) hScale
  have hMUpper : (M : ℝ) ≤ T ^ (1 + d - 1 / tau) := by
    calc
      (M : ℝ) ≤ T ^ (1 + d) / Q := by simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQEq, ← Real.rpow_sub hTPos]
  have hKernel := mediumTypeIStationaryKernel_le_rpow hsigma hsigmaUpper
    hTOne hQOne htauOne htauTwo hScale
  have hThresholdRaw := medium_reflected_threshold_explicit_lower
    (sigma := sigma) (T := T) (tau := tau) (d := d) (u := u)
    (eta := d) (Clog := Clog) (CK := CK) (Q := Q) (M := M)
    (by linarith) hTOne hQOne hMOne (by linarith) hScale hMUpper hClog
    hLogsM hCK (by simpa only [CK] using hKernel)
  have hThresholdExact :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) /
          Cref ≤ L := by
    simpa only [Cref, L, S, R, V, Q, M, hA] using hThresholdRaw
  have hExponent := medium_reflected_threshold_exponent_lower hsigma
    hsigmaUpper htauOne hd hdGap huD
  have hThreshold : T ^ g / Cref ≤ L := by
    have hPow := Real.rpow_le_rpow_of_exponent_le hTOne hExponent
    exact (div_le_div_of_nonneg_right hPow (zero_le_one.trans hCref)).trans (by
      simpa only [g, Cref, L, S, R, V, Q, M, hA] using hThresholdRaw)
  have hUNonempty : U.Nonempty := by
    by_contra hnot
    have hUZero : U.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hnot)
    rw [hUZero, mul_zero] at hCardU
    have hWCard : 0 < W.card := hW.card_pos
    omega
  have hLToP : L ≤ ((2 ^ j : ℕ) : ℝ) :=
    unit_coeff_threshold_le_dyadic_length hL.le hUNonempty hCoeff hLargeU
  have hScaleData := hScaleUpper hTScale hL hThreshold hLToP
  rcases hScaleData with ⟨hPOne, hTauPUpper⟩
  have hPLtM : 2 ^ j < M := by
    exact Nat.pow_lt_of_lt_clog (Finset.mem_range.mp hj)
  have hTauPLower := reflected_dyadic_scale_lower_of_expanded_cutoff
    (T := T) (τ := tau) (d := d) (Q := Q) (P := 2 ^ j) (M := M)
    (by linarith) hQOne hPOne htauOne htauTwo hd.le hScale hPLtM.le
      (by simpa only [M] using hMUpperRaw)
  refine ⟨j, hj, U, hSepU, hURange, hCardU, hCoeff,
    ?_, hPOne, hPLtM, hTauPLower, ?_, hThresholdExact, hThreshold⟩
  · simpa only [L, S, R, V, Q, M] using hLargeU
  · simpa only [Uscale] using hTauPUpper


end TaoTrudgianYang2025
