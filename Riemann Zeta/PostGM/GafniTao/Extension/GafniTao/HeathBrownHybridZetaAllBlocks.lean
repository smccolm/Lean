import GafniTao.HeathBrownHybridZetaLong

/-!
# Uniform hybrid bound for every block below the conductor

This file joins the coefficient-one-half estimate below `sqrt t` to the
fixed-saving Ford estimate between `sqrt t` and `t`.  The near-one range is
kept explicit because it is precisely the range needed in Pintz's proof.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Every dyadic block with left endpoint between `1024` and the physical
height satisfies the coefficient-one-half zeta exponent, uniformly in its
right-edge truncation. -/
theorem norm_fordShiftedWeightedBlock_zero_le_hybrid_zeta
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → sigma ≤ 1 →
      1 - 1 / 12000000 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N → (N : ℝ) ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨Cshort, hCshort, hshort⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_half_zeta hepsilon
  let C : ℝ := Cshort + fordQualitativeCoefficient
  have hC : 0 < C := by
    dsimp only [C]
    linarith [fordQualitativeCoefficient_nonneg]
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hsigmaUpper hsigmaNear hN hNR hR hNt
  have hNOne : 1 < N := by omega
  have htOne : 1 ≤ t := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    exact this.trans hNt
  let p : ℝ := heathBrownHalfZetaKappa *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hkappa : 0 ≤ heathBrownHalfZetaKappa := by
    unfold heathBrownHalfZetaKappa
    positivity
  have hp : 0 ≤ p := by
    dsimp only [p]
    have : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    positivity
  have htp : 1 ≤ t ^ p := Real.one_le_rpow htOne hp
  by_cases hshortRange : (N : ℝ) ^ 2 ≤ t
  · have hraw := hshort sigma t N R hsigma hsigmaUpper hN hNR hR hshortRange
    exact hraw.trans (by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        linarith [fordQualitativeCoefficient_nonneg]
      · positivity)
  · have hmiddle := norm_fordShiftedWeightedBlock_zero_le_middle
      hsigma hsigmaNear hN hNt (le_of_not_ge hshortRange) hNR hR
    calc
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
          fordQualitativeCoefficient := hmiddle
      _ ≤ C * 1 := by
        dsimp only [C]
        nlinarith [hCshort, fordQualitativeCoefficient_nonneg]
      _ ≤ C * t ^ p := mul_le_mul_of_nonneg_left htp hC.le
      _ = C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

/-- The same estimate for every positive block below the conductor.  The
finitely many blocks below `1024` are discharged by the proved qualitative
Ford theorem and absorbed into one uniform constant. -/
theorem norm_fordShiftedWeightedBlock_zero_le_all_zeta
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → sigma ≤ 1 →
      1 - 1 / 12000000 ≤ sigma →
      0 < N → N < R → R ≤ 2 * N → (N : ℝ) ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨Chybrid, hChybrid, hhybrid⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_hybrid_zeta hepsilon
  let C : ℝ := Chybrid + 1024 * fordQualitativeCoefficient
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [fordQualitativeCoefficient_nonneg]
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hsigmaUpper hsigmaNear hN hNR hR hNt
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htOne : 1 ≤ t := hNOne.trans hNt
  let p : ℝ := heathBrownHalfZetaKappa *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hkappa : 0 ≤ heathBrownHalfZetaKappa := by
    unfold heathBrownHalfZetaKappa
    positivity
  have hp : 0 ≤ p := by
    dsimp only [p]
    have : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by linarith) _
    positivity
  have htp : 1 ≤ t ^ p := Real.one_le_rpow htOne hp
  by_cases hlarge : 1024 ≤ N
  · have hraw := hhybrid sigma t N R hsigma hsigmaUpper hsigmaNear
      hlarge hNR hR hNt
    exact hraw.trans (by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        nlinarith [fordQualitativeCoefficient_nonneg]
      · positivity)
  · have hNtop : N ≤ 1024 := by omega
    have hraw := norm_fordShiftedWeightedBlock_zero_le_general
      ford_exponential_sum_qualitative fordQualitativeCoefficient_nonneg
      hsigma hN hNt hNR hR
    have hweight : ((N + 1 : ℕ) : ℝ) ^ (-sigma) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (show 1 ≤ N + 1 by omega)
      · linarith
    have hexponent :
        1 - 1 / (3000000 * fordLambda N t ^ 2) ≤ 1 := by
      have : 0 ≤ 1 / (3000000 * fordLambda N t ^ 2) := by positivity
      linarith
    have hpow : (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNOne hexponent
    have hmajorant :
        fordGeneralMajorant fordQualitativeCoefficient 3000000 N t ≤
          fordQualitativeCoefficient * (N : ℝ) := by
      unfold fordGeneralMajorant
      exact mul_le_mul_of_nonneg_left hpow fordQualitativeCoefficient_nonneg
    have hmajorantNonneg : 0 ≤
        fordGeneralMajorant fordQualitativeCoefficient 3000000 N t := by
      unfold fordGeneralMajorant
      exact mul_nonneg fordQualitativeCoefficient_nonneg
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) _)
    have hsmall :
        ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
          1024 * fordQualitativeCoefficient := by
      calc
        ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
            ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
              fordGeneralMajorant fordQualitativeCoefficient 3000000 N t := by
          simpa only [Nat.cast_add, Nat.cast_one] using hraw
        _ ≤ 1 * fordGeneralMajorant fordQualitativeCoefficient 3000000 N t :=
          mul_le_mul_of_nonneg_right hweight hmajorantNonneg
        _ ≤ 1 * (fordQualitativeCoefficient * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hmajorant (by norm_num)
        _ ≤ 1024 * fordQualitativeCoefficient := by
          rw [one_mul]
          have hNtopReal : (N : ℝ) ≤ 1024 := by exact_mod_cast hNtop
          nlinarith [fordQualitativeCoefficient_nonneg]
    calc
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
          1024 * fordQualitativeCoefficient := hsmall
      _ ≤ C * 1 := by
        dsimp only [C]
        nlinarith [hChybrid, fordQualitativeCoefficient_nonneg]
      _ ≤ C * t ^ p := mul_le_mul_of_nonneg_left htp hC.le
      _ = C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

#print axioms norm_fordShiftedWeightedBlock_zero_le_hybrid_zeta
#print axioms norm_fordShiftedWeightedBlock_zero_le_all_zeta

end

end GafniTao
