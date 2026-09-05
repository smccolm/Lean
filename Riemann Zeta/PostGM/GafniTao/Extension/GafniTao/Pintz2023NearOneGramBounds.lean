import GafniTao.Pintz2023HalaszConsumer

/-!
# Near-one bounds for the exact Pintz Gram kernel

The zero-distance upper bound `xi` and the auxiliary smoothing parameter
`eta` are deliberately distinct.  Pintz later lets the latter tend to zero;
identifying the two would incorrectly shrink the source range.
-/

open Complex

namespace GafniTao

noncomputable section

noncomputable def pintz2023NearOneGramMaxDistance
    (xi eta : ℝ) : ℝ :=
  2 * xi + 4 * eta

noncomputable def pintz2023NearOneGramExponent
    (xi eta epsilon : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (pintz2023NearOneGramMaxDistance xi eta) ^ (3 / 2 : ℝ) +
    epsilon

noncomputable def pintz2023NearOneDiagonalMajorant
    (C : ℝ) (N : ℕ) (xi eta : ℝ) : ℝ :=
  C * (4 * eta)⁻¹ *
    (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta

noncomputable def pintz2023NearOneOffDiagonalMajorant
    (C : ℝ) (N : ℕ) (xi eta epsilon T G : ℝ) : ℝ :=
  C * (4 * eta)⁻¹ *
    ((2 * T + 3) ^ pintz2023NearOneGramExponent xi eta epsilon +
      (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
        (2 * T + 2) * Real.exp (-(Real.pi * G) / 2))

private theorem abs_sub_le_two_mul_of_abs_le
    {x y T : ℝ} (hx : |x| ≤ T) (hy : |y| ≤ T) :
    |y - x| ≤ 2 * T := by
  calc
    |y - x| ≤ |y| + |x| := abs_sub y x
    _ ≤ T + T := add_le_add hy hx
    _ = 2 * T := by ring

/-- Uniform diagonal bound for all zero distances in `[0,xi]`. -/
theorem exists_pintz2023NearOneDiagonalMajorant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (xi eta etaJ gamma : ℝ),
      0 < N → 0 < eta →
      etaJ ∈ Set.Icc 0 xi →
      pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 12 →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaJ - etaJ - 4 * eta : ℝ) : ℂ) +
            I * (((gamma - gamma : ℝ) : ℂ)))‖ ≤
        pintz2023NearOneDiagonalMajorant C N xi eta := by
  obtain ⟨C, hC, hDiagonal⟩ :=
    exists_norm_pintz2023HalaszGram_diagonal_infinite_le
  refine ⟨C, hC, ?_⟩
  intro N xi eta etaJ gamma hN heta hetaJ hMax
  have hdLower : 4 * eta ≤ 2 * etaJ + 4 * eta := by
    nlinarith [hetaJ.1]
  have hdPos : 0 < 2 * etaJ + 4 * eta :=
    lt_of_lt_of_le (by positivity) hdLower
  have hdUpper :
      2 * etaJ + 4 * eta ≤ pintz2023NearOneGramMaxDistance xi eta := by
    unfold pintz2023NearOneGramMaxDistance
    nlinarith [hetaJ.2]
  have hRaw := hDiagonal N eta etaJ gamma hN hdPos (hdUpper.trans hMax)
  have hInv : (2 * etaJ + 4 * eta)⁻¹ ≤ (4 * eta)⁻¹ :=
    (inv_le_inv₀ hdPos (by positivity)).2 hdLower
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hPow :
      (N : ℝ) ^ (2 * etaJ + 4 * eta) ≤
        (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta :=
    Real.rpow_le_rpow_of_exponent_le hNOne hdUpper
  unfold pintz2023NearOneDiagonalMajorant
  calc
    _ ≤ C * (2 * etaJ + 4 * eta)⁻¹ *
        (N : ℝ) ^ (2 * etaJ + 4 * eta) := hRaw
    _ ≤ C * (4 * eta)⁻¹ *
        (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta := by
      gcongr

/-- Uniform off-diagonal bound obtained from the literal Mellin/zeta
estimate.  The last term retains the exact exponential decay in the
separation `G`; it is not replaced by an unspecified negligible error. -/
theorem exists_pintz2023NearOneOffDiagonalMajorant
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (xi eta etaJ etaK gamma delta T G : ℝ),
      0 < N → 0 < eta →
      etaJ ∈ Set.Icc 0 xi → etaK ∈ Set.Icc 0 xi →
      pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 12 →
      1 ≤ T → 1 ≤ G → |gamma| ≤ T → |delta| ≤ T →
      G ≤ |delta - gamma| →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
            I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        pintz2023NearOneOffDiagonalMajorant
          C N xi eta epsilon T G := by
  obtain ⟨B, R, hB, hR, hBound⟩ :=
    exists_norm_pintz2023SmoothedZetaSum_nearOne_le
      hepsilon hepsilonUpper
  let C : ℝ := max B R
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N xi eta etaJ etaK gamma delta T G hN heta
    hetaJ hetaK hMax hT hG hgamma hdelta hSep
  let d : ℝ := etaJ + etaK + 4 * eta
  let p : ℝ := (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon
  let pMax : ℝ := pintz2023NearOneGramExponent xi eta epsilon
  have hdLower : 4 * eta ≤ d := by
    dsimp only [d]
    nlinarith [hetaJ.1, hetaK.1]
  have hdPos : 0 < d := lt_of_lt_of_le (by positivity) hdLower
  have hdUpper : d ≤ pintz2023NearOneGramMaxDistance xi eta := by
    dsimp only [d]
    unfold pintz2023NearOneGramMaxDistance
    nlinarith [hetaJ.2, hetaK.2]
  have hsigmaLower : 11 / 12 ≤ 1 - d := by linarith
  have hsigmaUpper : 1 - d < 1 := by linarith
  have htAbs : |delta - gamma| ≤ 2 * T :=
    abs_sub_le_two_mul_of_abs_le hgamma hdelta
  have htOne : 1 ≤ |delta - gamma| := hG.trans hSep
  have hRaw := hBound N (1 - d) (delta - gamma) hN
    hsigmaLower hsigmaUpper htOne
  have hArg :
      (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
          I * (((delta - gamma : ℝ) : ℂ))) =
        (((1 - d : ℝ) : ℂ) + I * (((delta - gamma : ℝ) : ℂ))) := by
    apply Complex.ext
    · simp [d]
      ring
    · simp
  rw [hArg]
  have hInv : d⁻¹ ≤ (4 * eta)⁻¹ :=
    (inv_le_inv₀ hdPos (by positivity)).2 hdLower
  have hdPow :
      d ^ (3 / 2 : ℝ) ≤
        (pintz2023NearOneGramMaxDistance xi eta) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hdPos.le hdUpper (by norm_num)
  have hpNonneg : 0 ≤ p := by dsimp only [p]; positivity
  have hpMax : p ≤ pMax := by
    dsimp only [p, pMax, pintz2023NearOneGramExponent]
    linarith
  have hHeightBase : 1 ≤ 2 * T + 3 := by linarith
  have hHeight : |delta - gamma| + 3 ≤ 2 * T + 3 := by linarith
  have hHeightPow :
      (|delta - gamma| + 3) ^ p ≤ (2 * T + 3) ^ pMax := by
    calc
      _ ≤ (2 * T + 3) ^ p :=
        Real.rpow_le_rpow (by positivity) hHeight hpNonneg
      _ ≤ (2 * T + 3) ^ pMax :=
        Real.rpow_le_rpow_of_exponent_le hHeightBase hpMax
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNPow :
      (N : ℝ) ^ d ≤
        (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta :=
    Real.rpow_le_rpow_of_exponent_le hNOne hdUpper
  have hHeightTwo : |delta - gamma| + 2 ≤ 2 * T + 2 := by linarith
  have hExp :
      Real.exp (-(Real.pi * |delta - gamma|) / 2) ≤
        Real.exp (-(Real.pi * G) / 2) := by
    apply Real.exp_le_exp.mpr
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hBC : B ≤ C := le_max_left _ _
  have hRC : R ≤ C := le_max_right _ _
  have hMain :
      B * d⁻¹ * (|delta - gamma| + 3) ^ p ≤
        C * (4 * eta)⁻¹ * (2 * T + 3) ^ pMax := by
    gcongr
  have hResidue :
      R * d⁻¹ * (N : ℝ) ^ d * (|delta - gamma| + 2) *
          Real.exp (-(Real.pi * |delta - gamma|) / 2) ≤
        C * (4 * eta)⁻¹ *
          ((N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
            (2 * T + 2) * Real.exp (-(Real.pi * G) / 2)) := by
    have hCoeff : R * d⁻¹ ≤ C * (4 * eta)⁻¹ := by
      exact mul_le_mul hRC hInv (by positivity) hC.le
    calc
      R * d⁻¹ * (N : ℝ) ^ d * (|delta - gamma| + 2) *
          Real.exp (-(Real.pi * |delta - gamma|) / 2) ≤
        (C * (4 * eta)⁻¹) * (N : ℝ) ^ d *
          (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2) := by
        gcongr
      _ ≤ (C * (4 * eta)⁻¹) *
          (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
            (2 * T + 2) * Real.exp (-(Real.pi * G) / 2) := by
        gcongr
      _ = C * (4 * eta)⁻¹ *
          ((N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
            (2 * T + 2) * Real.exp (-(Real.pi * G) / 2)) := by ring
  unfold pintz2023NearOneOffDiagonalMajorant
  have hRaw' :
      ‖pintz2023SmoothedZetaSum N
          (((1 - d : ℝ) : ℂ) + I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        B * d⁻¹ * (|delta - gamma| + 3) ^ p +
          R * d⁻¹ * (N : ℝ) ^ d * (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2) := by
    simpa [d, p] using hRaw
  calc
    _ ≤ B * d⁻¹ * (|delta - gamma| + 3) ^ p +
          R * d⁻¹ * (N : ℝ) ^ d * (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2) := hRaw'
    _ ≤ C * (4 * eta)⁻¹ * (2 * T + 3) ^ pMax +
          C * (4 * eta)⁻¹ *
            ((N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
              (2 * T + 2) * Real.exp (-(Real.pi * G) / 2)) :=
      add_le_add hMain hResidue
    _ = C * (4 * eta)⁻¹ *
        ((2 * T + 3) ^ pintz2023NearOneGramExponent xi eta epsilon +
          (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
            (2 * T + 2) * Real.exp (-(Real.pi * G) / 2)) := by
      dsimp only [pMax]
      ring

#print axioms exists_pintz2023NearOneDiagonalMajorant
#print axioms exists_pintz2023NearOneOffDiagonalMajorant

end

end GafniTao
