import GafniTao.Pintz2023TwoScaleDecay

/-!
# Pintz (2023), equation (4.20)

This file applies the corrected two-scale exponent argument to the literal
local-frequency Mellin bound.  The moving-pole residue remains a separate,
fully explicit summand for the subsequent source-scale absorption.
-/

open Complex

namespace GafniTao

noncomputable section

/-- Energy-weighted local Gram majorant in the complementary branch to
Corollary 3.  The first summand is the exact `T^(-epsilon/k)` saving; the
second is the unabsorbed moving-pole residue. -/
theorem exists_pintz2023_equation420_weighted_gram_native
    {eta target : ℝ} {k ell : ℕ}
    (hcell : PintzCell eta k ell)
    (data : Pintz2023PowerMarginData eta target k ell) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (etaJ etaK gamma delta S : ℝ),
      0 < N → etaJ ∈ Set.Icc 0 eta → etaK ∈ Set.Icc 0 eta →
      1 ≤ |delta - gamma| → 1 ≤ S →
      S ^ pintz2023EllThreshold eta data.epsilon ell ≤ (N : ℝ) →
      |delta - gamma| ^ (19 / (10 * (ell : ℝ))) ≤ (N : ℝ) →
      (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        C * (4 * eta)⁻¹ *
          (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon *
              S ^ (-data.epsilon / (k : ℝ)) +
            (N : ℝ) ^ (2 * eta) * (|delta - gamma| + 2) *
              Real.exp (-(Real.pi * |delta - gamma|) / 2)) := by
  obtain ⟨C, hC, hLocal⟩ :=
    exists_pintz2023LocalOffDiagonalMajorant
      data.epsilon_pos data.epsilon_le_one
  refine ⟨C, hC, ?_⟩
  intro N etaJ etaK gamma delta S hN hetaJ hetaK hSep hS
    hCritical hFrequency
  have heta : 0 < eta := pintzCell_eta_pos hcell
  have hMax : pintz2023NearOneGramMaxDistance eta eta ≤ 1 / 4 := by
    unfold pintz2023NearOneGramMaxDistance
    nlinarith [data.eta_le_one_twentyFour]
  have hRaw := hLocal N eta eta etaJ etaK gamma delta hN heta
    hetaJ hetaK hMax hSep
  let p : ℝ := pintz2023NearOneGramExponent eta eta data.epsilon
  have hp : 0 ≤ p := by
    dsimp only [p, pintz2023NearOneGramExponent,
      pintz2023NearOneGramMaxDistance]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
      data.epsilon_pos.le
  have htPos : 0 < |delta - gamma| := zero_lt_one.trans_le hSep
  have htFour : |delta - gamma| + 3 ≤ 4 * |delta - gamma| := by
    nlinarith
  have hMainBase :
      (|delta - gamma| + 3) ^ p ≤
        4 ^ p * |delta - gamma| ^ p := by
    calc
      (|delta - gamma| + 3) ^ p ≤
          (4 * |delta - gamma|) ^ p :=
        Real.rpow_le_rpow (by positivity) htFour hp
      _ = 4 ^ p * |delta - gamma| ^ p := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]
  have hDecay := pintz2023_equation420_two_scale_decay
    hcell data hSep hS hCritical hFrequency
  have hMain :
      (N : ℝ) ^ (-4 * eta) * (|delta - gamma| + 3) ^ p ≤
        4 ^ p * S ^ (-data.epsilon / (k : ℝ)) := by
    calc
      (N : ℝ) ^ (-4 * eta) * (|delta - gamma| + 3) ^ p ≤
          (N : ℝ) ^ (-4 * eta) *
            (4 ^ p * |delta - gamma| ^ p) := by
        gcongr
      _ = 4 ^ p *
          ((N : ℝ) ^ (-4 * eta) * |delta - gamma| ^ p) := by ring
      _ ≤ 4 ^ p * S ^ (-data.epsilon / (k : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [p] using hDecay) (Real.rpow_nonneg (by norm_num) _)
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hResiduePower :
      (N : ℝ) ^ (-4 * eta) *
          (N : ℝ) ^ pintz2023NearOneGramMaxDistance eta eta =
        (N : ℝ) ^ (2 * eta) := by
    rw [← Real.rpow_add hNPos]
    unfold pintz2023NearOneGramMaxDistance
    congr 1
    ring
  have hWeightedRaw :
      (N : ℝ) ^ (-4 * eta) *
          ‖pintz2023SmoothedZetaSum N
            (((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
              I * (((delta - gamma : ℝ) : ℂ)))‖ ≤
        (N : ℝ) ^ (-4 * eta) *
          pintz2023LocalOffDiagonalMajorant C N eta eta data.epsilon
            (delta - gamma) :=
    mul_le_mul_of_nonneg_left hRaw (Real.rpow_nonneg hNPos.le _)
  unfold pintz2023LocalOffDiagonalMajorant at hWeightedRaw
  calc
    _ ≤ (N : ℝ) ^ (-4 * eta) *
        (C * (4 * eta)⁻¹ *
          ((|delta - gamma| + 3) ^ p +
            (N : ℝ) ^ pintz2023NearOneGramMaxDistance eta eta *
              (|delta - gamma| + 2) *
                Real.exp (-(Real.pi * |delta - gamma|) / 2))) := hWeightedRaw
    _ = C * (4 * eta)⁻¹ *
        ((N : ℝ) ^ (-4 * eta) * (|delta - gamma| + 3) ^ p +
          ((N : ℝ) ^ (-4 * eta) *
            (N : ℝ) ^ pintz2023NearOneGramMaxDistance eta eta) *
              (|delta - gamma| + 2) *
                Real.exp (-(Real.pi * |delta - gamma|) / 2)) := by ring
    _ ≤ C * (4 * eta)⁻¹ *
        (4 ^ p * S ^ (-data.epsilon / (k : ℝ)) +
          (N : ℝ) ^ (2 * eta) * (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2)) := by
      rw [hResiduePower]
      gcongr
    _ = C * (4 * eta)⁻¹ *
        (4 ^ pintz2023NearOneGramExponent eta eta data.epsilon *
            S ^ (-data.epsilon / (k : ℝ)) +
          (N : ℝ) ^ (2 * eta) * (|delta - gamma| + 2) *
            Real.exp (-(Real.pi * |delta - gamma|) / 2)) := by rfl

#print axioms exists_pintz2023_equation420_weighted_gram_native

end

end GafniTao
