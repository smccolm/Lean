import GafniTao.Pintz2023HalaszInfinite

/-!
# Quantitative bounds for Pintz's infinite Halasz Gram entries

The off-diagonal estimate in Pintz (4.19) is only useful after the diagonal
has also been estimated at the infinite ambient limit.  A cutoff-dependent
harmonic bound cannot be sent to infinity.  Here the diagonal is instead
estimated from the exact Mellin identity: its moving-pole residue contributes
the source-sized factor `N^d / d`, while the shifted contour is uniformly
smaller by the same majorant.
-/

open Complex

namespace GafniTao

noncomputable section

/-- The moving-pole residue at height zero.  This is the missing endpoint of
the residue estimate in `Pintz2023MellinResidue`, whose exponential version
is stated only for nonzero height. -/
theorem norm_pintz2023MellinWeight_real_nearOne_le
    {N : ℕ} (hN : 0 < N) {d : ℝ} (hd : 0 < d) (hdUpper : d ≤ 1 / 4) :
    ‖pintz2023MellinWeight N (d : ℂ)‖ ≤
      3 * d⁻¹ * (N : ℝ) ^ d := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hPower := norm_pintz2023MellinPowerDiff_nearOne_le
    (N := N) hN (d := d) (t := 0) (by linarith)
  have hGammaSucc : ‖Complex.Gamma ((d : ℂ) + 1)‖ ≤ 1 := by
    apply Complex.Gamma.norm_le_one
    · simp
      linarith
    · simp
      linarith
  have hRec := Complex.Gamma_add_one (d : ℂ) hdC
  have hGammaScaled : d * ‖Complex.Gamma (d : ℂ)‖ ≤ 1 := by
    rw [hRec, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hd] at hGammaSucc
    exact hGammaSucc
  have hGamma : ‖Complex.Gamma (d : ℂ)‖ ≤ d⁻¹ := by
    have hDiv : ‖Complex.Gamma (d : ℂ)‖ ≤ 1 / d :=
      (le_div_iff₀ hd).2 (by simpa [mul_comm] using hGammaScaled)
    simpa [div_eq_mul_inv] using hDiv
  rw [pintz2023MellinWeight_eq hdC, norm_mul]
  calc
    ‖pintz2023MellinPowerDiff N (d : ℂ)‖ * ‖Complex.Gamma (d : ℂ)‖ ≤
        (3 * (N : ℝ) ^ d) * d⁻¹ := by
      simpa using mul_le_mul hPower hGamma (norm_nonneg _)
        (by positivity : 0 ≤ 3 * (N : ℝ) ^ d)
    _ = 3 * d⁻¹ * (N : ℝ) ^ d := by ring

/-- Uniform infinite diagonal estimate in the strict near-one strip.  Unlike
the preliminary finite-cutoff estimate, this theorem has no divergent
ambient cutoff. -/
theorem exists_norm_pintz2023SmoothedZetaSum_real_nearOne_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (d : ℝ),
      0 < N → 0 < d → d ≤ 1 / 4 →
      ‖pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ)‖ ≤
        C * d⁻¹ * (N : ℝ) ^ d := by
  obtain ⟨B, hB, hMain⟩ :=
    exists_norm_pintz2023SmoothedZetaSum_sub_residue_nearOne_le
      (epsilon := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  let C : ℝ := 3 * (B + 1)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N d hN hd hdUpper
  let sigma : ℝ := 1 - d
  have hsigmaLower : 3 / 4 ≤ sigma := by
    dsimp only [sigma]
    linarith
  have hsigmaUpper : sigma < 1 := by
    dsimp only [sigma]
    linarith
  have hMain' :
      ‖pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ) -
          pintz2023MellinWeight N (d : ℂ)‖ ≤
        B * d⁻¹ *
          (3 : ℝ) ^ ((1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + 1 / 2) := by
    simpa [sigma] using hMain N sigma 0 hN hsigmaLower hsigmaUpper
  have hpNonneg : 0 ≤ (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + 1 / 2 := by
    positivity
  have hdOne : d ≤ 1 := hdUpper.trans (by norm_num)
  have hdPow : d ^ (3 / 2 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_one hd.le hdOne (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hpUpper : (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + 1 / 2 ≤ 1 := by
    linarith
  have hThreePow :
      (3 : ℝ) ^ ((1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + 1 / 2) ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hpUpper
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpow : 1 ≤ (N : ℝ) ^ d := Real.one_le_rpow hNReal hd.le
  have hResidue := norm_pintz2023MellinWeight_real_nearOne_le hN hd hdUpper
  have hMainBound :
      ‖pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ) -
          pintz2023MellinWeight N (d : ℂ)‖ ≤
        3 * B * d⁻¹ * (N : ℝ) ^ d := by
    calc
      _ ≤ B * d⁻¹ *
          (3 : ℝ) ^ ((1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + 1 / 2) := by
        simpa [sigma] using hMain'
      _ ≤ B * d⁻¹ * 3 := by
        gcongr
      _ ≤ 3 * B * d⁻¹ * (N : ℝ) ^ d := by
        have hBd : 0 ≤ 3 * B * d⁻¹ := by positivity
        calc
          B * d⁻¹ * 3 = 3 * B * d⁻¹ * 1 := by ring
          _ ≤ 3 * B * d⁻¹ * (N : ℝ) ^ d :=
            mul_le_mul_of_nonneg_left hNpow hBd
  calc
    ‖pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ)‖ =
        ‖(pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ) -
            pintz2023MellinWeight N (d : ℂ)) +
          pintz2023MellinWeight N (d : ℂ)‖ := by ring_nf
    _ ≤ ‖pintz2023SmoothedZetaSum N ((1 - d : ℝ) : ℂ) -
          pintz2023MellinWeight N (d : ℂ)‖ +
        ‖pintz2023MellinWeight N (d : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 * B * d⁻¹ * (N : ℝ) ^ d +
        3 * d⁻¹ * (N : ℝ) ^ d := add_le_add hMainBound hResidue
    _ = C * d⁻¹ * (N : ℝ) ^ d := by
      dsimp only [C]
      ring

/-- Diagonal specialization in the variables used by Pintz (4.19). -/
theorem exists_norm_pintz2023HalaszGram_diagonal_infinite_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (eta etaJ gamma : ℝ),
      0 < N → 0 < 2 * etaJ + 4 * eta →
      2 * etaJ + 4 * eta ≤ 1 / 4 →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ) +
            I * (((gamma - gamma : ℝ) : ℂ)))‖ ≤
        C * (2 * etaJ + 4 * eta)⁻¹ *
          (N : ℝ) ^ (2 * etaJ + 4 * eta) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_norm_pintz2023SmoothedZetaSum_real_nearOne_le
  refine ⟨C, hC, ?_⟩
  intro N eta etaJ gamma hN hd hdUpper
  have hArg :
      (((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ) +
          I * (((gamma - gamma : ℝ) : ℂ))) =
        (((1 - (2 * etaJ + 4 * eta) : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hArg]
  exact hBound N (2 * etaJ + 4 * eta) hN hd hdUpper

#print axioms norm_pintz2023MellinWeight_real_nearOne_le
#print axioms exists_norm_pintz2023SmoothedZetaSum_real_nearOne_le
#print axioms exists_norm_pintz2023HalaszGram_diagonal_infinite_le

end

end GafniTao
