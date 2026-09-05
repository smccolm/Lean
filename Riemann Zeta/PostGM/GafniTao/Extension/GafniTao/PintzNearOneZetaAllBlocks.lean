import GafniTao.PintzNearOneZetaMiddle
import GafniTao.FordQualitativeFiniteZeta

/-!
# Uniform Pintz near-one estimate for every dyadic block

The short and conductor-scale estimates are joined at `N^2 = t`; the
finitely many blocks below `1024` are absorbed with the already proved
qualitative Ford majorant.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Every block with left endpoint at least `1024` and at most the ordinate
satisfies the coefficient-one-half Pintz estimate. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_hybrid
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 11 / 12 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N → (N : ℝ) ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨Cshort, hCshort, hshort⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne hepsilon
  let C : ℝ := Cshort + 130
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
  have htNonneg : 0 ≤ t := by
    have : (0 : ℝ) ≤ N := by positivity
    exact this.trans hNt
  have hpow : 0 ≤ t ^ ((1 / 2 : ℝ) *
      (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) :=
    Real.rpow_nonneg htNonneg _
  by_cases hshortRange : (N : ℝ) ^ 2 ≤ t
  · have hraw := hshort sigma t N R hsigmaUpper hsigmaLower
      hN hNR hR hshortRange
    exact hraw.trans (mul_le_mul_of_nonneg_right (by
      dsimp only [C]
      linarith) hpow)
  · have hmiddle :=
      norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle
        hepsilon hsigmaUpper hsigmaLower hN hNt
          (le_of_not_ge hshortRange) hNR hR
    exact hmiddle.trans (mul_le_mul_of_nonneg_right (by
      dsimp only [C]
      linarith) hpow)

/-- Full block estimate, including the finite initial dyadic range. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_all
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 11 / 12 ≤ sigma →
      0 < N → N < R → R ≤ 2 * N → (N : ℝ) ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨Chybrid, hChybrid, hhybrid⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_hybrid hepsilon
  let C : ℝ := Chybrid + 1024 * fordQualitativeCoefficient
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [fordQualitativeCoefficient_nonneg]
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
  have hsigma : 0 ≤ sigma := by linarith
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htOne : 1 ≤ t := hNOne.trans hNt
  let p : ℝ := (1 / 2 : ℝ) *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hp : 0 ≤ p := by
    dsimp only [p]
    have hu : 0 ≤ 1 - sigma := by linarith
    positivity
  have htp : 1 ≤ t ^ p := Real.one_le_rpow htOne hp
  by_cases hlarge : 1024 ≤ N
  · have hraw := hhybrid sigma t N R hsigmaUpper hsigmaLower
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
    have hpowN : (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNOne hexponent
    have hmajorant :
        fordGeneralMajorant fordQualitativeCoefficient 3000000 N t ≤
          fordQualitativeCoefficient * (N : ℝ) := by
      unfold fordGeneralMajorant
      exact mul_le_mul_of_nonneg_left hpowN fordQualitativeCoefficient_nonneg
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
      _ = C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_hybrid
#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_all

end

end GafniTao
