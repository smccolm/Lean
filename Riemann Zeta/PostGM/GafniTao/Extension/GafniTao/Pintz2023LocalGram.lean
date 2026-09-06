import GafniTao.Pintz2023NearOneGramBounds

/-!
# Pintz (2023), equation (4.20): the local-frequency Gram bound

The ambient-height majorant used elsewhere is too coarse for the first case
of Pintz's equation (4.20).  This file retains the actual frequency
`|delta - gamma|` in both the zeta term and the moving-pole residue.  The
subsequent scale argument may therefore use the simultaneous lower bounds
coming from `A_h` and from `B_h \gg |delta-gamma|^(1.9/ell)`.
-/

open Complex

namespace GafniTao

noncomputable section

/-- The literal local-frequency majorant furnished by the Mellin-residue
formula and Heath-Brown's zeta estimate. -/
noncomputable def pintz2023LocalOffDiagonalMajorant
    (C : ℝ) (N : ℕ) (xi eta epsilon t : ℝ) : ℝ :=
  C * (4 * eta)⁻¹ *
    ((|t| + 3) ^ pintz2023NearOneGramExponent xi eta epsilon +
      (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
        (|t| + 2) * Real.exp (-(Real.pi * |t|) / 2))

/-- Source-local form of Pintz Lemma 3.4.  Unlike the global convenience
bound, this theorem does not replace `|delta-gamma|` by `2*T`. -/
theorem exists_pintz2023LocalOffDiagonalMajorant
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (xi eta etaJ etaK gamma delta : ℝ),
      0 < N → 0 < eta →
      etaJ ∈ Set.Icc 0 xi → etaK ∈ Set.Icc 0 xi →
      pintz2023NearOneGramMaxDistance xi eta ≤ 1 / 4 →
      1 ≤ |delta - gamma| →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
            I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        pintz2023LocalOffDiagonalMajorant
          C N xi eta epsilon (delta - gamma) := by
  obtain ⟨B, R, hB, hR, hBound⟩ :=
    exists_norm_pintz2023SmoothedZetaSum_nearOne_le
      hepsilon hepsilonUpper
  let C : ℝ := max B R
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro N xi eta etaJ etaK gamma delta hN heta hetaJ hetaK hMax hSep
  let d : ℝ := etaJ + etaK + 4 * eta
  let p : ℝ := (1 / 2 : ℝ) * d ^ (3 / 2 : ℝ) + epsilon
  let dMax : ℝ := pintz2023NearOneGramMaxDistance xi eta
  let pMax : ℝ := pintz2023NearOneGramExponent xi eta epsilon
  have hdLower : 4 * eta ≤ d := by
    dsimp only [d]
    nlinarith [hetaJ.1, hetaK.1]
  have hdPos : 0 < d := lt_of_lt_of_le (by positivity) hdLower
  have hdUpper : d ≤ dMax := by
    dsimp only [d, dMax]
    unfold pintz2023NearOneGramMaxDistance
    nlinarith [hetaJ.2, hetaK.2]
  have hsigmaLower : 3 / 4 ≤ 1 - d := by
    have hMax' : dMax ≤ 1 / 4 := by simpa only [dMax] using hMax
    linarith
  have hsigmaUpper : 1 - d < 1 := by linarith
  have hRaw := hBound N (1 - d) (delta - gamma) hN
    hsigmaLower hsigmaUpper hSep
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
      d ^ (3 / 2 : ℝ) ≤ dMax ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hdPos.le hdUpper (by norm_num)
  have hpMax : p ≤ pMax := by
    dsimp only [p, pMax, pintz2023NearOneGramExponent]
    linarith
  have hFreqBase : 1 ≤ |delta - gamma| + 3 := by
    nlinarith [abs_nonneg (delta - gamma)]
  have hFreqPow :
      (|delta - gamma| + 3) ^ p ≤
        (|delta - gamma| + 3) ^ pMax :=
    Real.rpow_le_rpow_of_exponent_le hFreqBase hpMax
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNPow : (N : ℝ) ^ d ≤ (N : ℝ) ^ dMax :=
    Real.rpow_le_rpow_of_exponent_le hNOne hdUpper
  have hBC : B ≤ C := le_max_left _ _
  have hRC : R ≤ C := le_max_right _ _
  have hMain :
      B * d⁻¹ * (|delta - gamma| + 3) ^ p ≤
        C * (4 * eta)⁻¹ * (|delta - gamma| + 3) ^ pMax := by
    gcongr
  have hResidue :
      R * d⁻¹ * (N : ℝ) ^ d * (|delta - gamma| + 2) *
          Real.exp (-(Real.pi * |delta - gamma|) / 2) ≤
        C * (4 * eta)⁻¹ * (N : ℝ) ^ dMax *
          (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2) := by
    gcongr
  unfold pintz2023LocalOffDiagonalMajorant
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
    _ ≤ C * (4 * eta)⁻¹ * (|delta - gamma| + 3) ^ pMax +
          C * (4 * eta)⁻¹ * (N : ℝ) ^ dMax *
            (|delta - gamma| + 2) *
              Real.exp (-(Real.pi * |delta - gamma|) / 2) :=
      add_le_add hMain hResidue
    _ = C * (4 * eta)⁻¹ *
        ((|delta - gamma| + 3) ^
            pintz2023NearOneGramExponent xi eta epsilon +
          (N : ℝ) ^ pintz2023NearOneGramMaxDistance xi eta *
            (|delta - gamma| + 2) *
              Real.exp (-(Real.pi * |delta - gamma|) / 2)) := by
      dsimp only [dMax, pMax]
      ring

#print axioms exists_pintz2023LocalOffDiagonalMajorant

end

end GafniTao
