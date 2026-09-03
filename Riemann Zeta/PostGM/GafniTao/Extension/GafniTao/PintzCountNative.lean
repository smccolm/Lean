import GafniTao.PintzPhysicalNative

/-!
# A division-free-to-count form of the native Pintz estimate

The adaptive detector square is at least four in the source range.  This
allows the finite inequality to be converted back to the literal analytic-
multiplicity zero count without retaining a reciprocal detector term.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem one_le_harmonic_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    (1 : ℝ) ≤ (harmonic n : ℝ) := by
  have hq : (1 : ℚ) ≤ harmonic n := by
    rw [harmonic_eq_sum_Icc]
    calc
      (1 : ℚ) = ((1 : ℕ) : ℚ)⁻¹ := by norm_num
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ((i : ℚ)⁻¹) := by
        apply Finset.single_le_sum
          (s := Finset.Icc 1 n) (f := fun i : ℕ => ((i : ℚ)⁻¹))
        · intro i hi
          positivity
        · simp [hn]
  exact_mod_cast hq

theorem one_le_pintzGramCore
    {eta T : ℝ} (hT : 1 / 4 ≤ T) :
    1 ≤ pintzGramCore eta T := by
  unfold pintzGramCore
  have hlog : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ (4 * T) ^ (fordSourceB 3000000 *
      (4 * eta) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hparen : 0 ≤ 1 +
      1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (4 * T) ^ (2 / 3 : ℝ) := by positivity
  exact le_add_of_nonneg_right
    (mul_nonneg fordQualitativeCoefficient_nonneg (mul_nonneg hpow hparen))

theorem four_le_pintzDetectorSquareLower
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1)
    (hTbase : Real.exp (Real.exp 1) ≤ T)
    (hTabsorb : pintzCoreAbsorptionHeight c ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    4 ≤ pintzDetectorSquareLower c eta T := by
  have hcore := pintz_core_absorbed_by_detector_square
    hc heta hetaUpper hTbase hTabsorb hetaAbove
  have hH : (1 : ℝ) ≤
      (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) :=
    one_le_harmonic_of_one_le (pintzMobiusCutoff_one_le _)
  have hTQuarter : (1 / 4 : ℝ) ≤ T := by
    have hone : (1 : ℝ) ≤ Real.exp (Real.exp 1) :=
      Real.one_le_exp (Real.exp_pos 1).le
    linarith
  have hCoreOne := one_le_pintzGramCore (eta := eta) hTQuarter
  nlinarith [mul_nonneg (by linarith : 0 ≤
    (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ))
    (by linarith : 0 ≤ pintzGramCore eta T)]

theorem pintz_zeroCount_native_bound
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hBasic : max (Real.exp 2) 8 ≤ T)
    (hErrorHeight : pintzContourErrorHeight c ≤ T)
    (hCoreHeight : pintzCoreAbsorptionHeight c ≤ T)
    (hLambdaHeight : 2 * pintzDensityLambda eta T ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (zeroCount (1 - eta) T : ℝ) ≤
      (2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
        Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) +
      (pintzSelectionLoss (2 * pintzDensityLambda eta T)
          (pintzAdaptiveSeparation c eta T) T : ℝ) *
        ((harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) ^ 2 *
          (pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
            (4 * eta) / 2) := by
  let V := pintzDetectedLowerBound eta (pintzDensityLambda eta T) T
  let C₀ : ℝ :=
    (2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
      Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ)
  let R : ℝ :=
    (pintzSelectionLoss (2 * pintzDensityLambda eta T)
        (pintzAdaptiveSeparation c eta T) T : ℝ) *
      (2 * (harmonic (pintzMobiusCutoff
          (pintzDensityLambda eta T)) : ℝ) *
        ((pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
            (4 * eta) *
          (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ)))
  have hfinite := pintz_physical_finite_density_native hc heta hetaUpper
    hBasic hErrorHeight hCoreHeight hLambdaHeight hetaAbove
  have hBase : Real.exp (Real.exp 1) ≤ T := by
    unfold pintzContourErrorHeight at hErrorHeight
    exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hErrorHeight
  have hSquareLower := four_le_pintzDetectorSquareLower
    hc heta (by linarith) hBase hCoreHeight hetaAbove
  have hDetectedLower := pintzDetectorSquareLower_le_detected
    hc heta (by linarith) hBase hetaAbove
  have hVfour : 4 ≤ V ^ 2 := hSquareLower.trans hDetectedLower
  have hVpos : 0 < V := by
    unfold V pintzDetectedLowerBound
    have hT8 : (8 : ℝ) ≤ T := (le_max_right (Real.exp 2) 8).trans hBasic
    have hZ := pintzPhysicalZetaMajorant_pos (eta := eta) (T := T)
      (by linarith)
    have hlambda : 0 < pintzDensityLambda eta T := by
      have hExp : Real.exp 1 ≤ T :=
        (Real.exp_le_exp.mpr
          (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hBase
      exact pintzDensityLambda_pos heta.le hExp
    exact one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) hlambda)
        (mul_pos (div_pos hZ heta) (Real.exp_pos _)))
  have hR : 0 ≤ R := by
    dsimp [R]
    have hH : 0 ≤
        (harmonic (pintzMobiusCutoff (pintzDensityLambda eta T)) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      positivity
    positivity
  change (zeroCount (1 - eta) T : ℝ) * V ^ 2 ≤ C₀ * V ^ 2 + R
    at hfinite
  have hCount : (zeroCount (1 - eta) T : ℝ) ≤ C₀ + R / V ^ 2 := by
    calc
      (zeroCount (1 - eta) T : ℝ) ≤
          (C₀ * V ^ 2 + R) / V ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hVpos)).2 hfinite
      _ = C₀ + R / V ^ 2 := by
        field_simp [hVpos.ne']
  have hRquarter : R / V ^ 2 ≤ R / 4 := by
    exact div_le_div_of_nonneg_left hR (by norm_num) hVfour
  calc
    (zeroCount (1 - eta) T : ℝ) ≤ C₀ + R / V ^ 2 := hCount
    _ ≤ C₀ + R / 4 := by gcongr
    _ = _ := by
      dsimp [C₀, R]
      ring

#print axioms four_le_pintzDetectorSquareLower
#print axioms pintz_zeroCount_native_bound

end

end GafniTao
