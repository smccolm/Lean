import GafniTao.HeathBrownHybridZetaBlock
import GafniTao.FordQualitativeFiniteZeta

/-!
# The conductor-scale half of Heath--Brown's zeta estimate

For a block with `N <= t <= N^2`, the logarithmic scale
`tau = log t / log N` lies in `[1,2]`.  Consequently even the deliberately
non-optimized qualitative Ford estimate has a fixed saving on this range.
When `1 - sigma <= 1 / 12000000`, that saving absorbs the entire factor
`N^(1-sigma)`.  This is the second half of the hybrid block estimate used in
Pintz (4.9) and (4.20).
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A conductor-scale block has Ford logarithmic scale at most two. -/
theorem fordLambda_le_two_of_le_sq
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ 2) :
    fordLambda N t ≤ 2 := by
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  apply (Real.rpow_le_rpow_left_iff hNReal).mp
  rw [rpow_fordLambda_eq hN ht, Real.rpow_two]
  simpa only [sq] using htN

/-- On logarithmic scales at most two, the qualitative Ford saving is at
least `1/12000000`. -/
theorem one_div_twelveMillion_le_fordSaving
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    (1 : ℝ) / 12000000 ≤
      1 / (3000000 * fordLambda N t ^ 2) := by
  have htOne : 1 < t := by
    have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
    exact hNReal.trans_le hNt
  have htauLower : 1 ≤ fordLambda N t := one_le_fordLambda hN hNt
  have htauUpper : fordLambda N t ≤ 2 :=
    fordLambda_le_two_of_le_sq hN ht htN
  have htauSq : fordLambda N t ^ 2 ≤ 4 := by nlinarith
  have hdenPos : 0 < 3000000 * fordLambda N t ^ 2 := by
    have : 0 < fordLambda N t := zero_lt_one.trans_le htauLower
    positivity
  have hden : 3000000 * fordLambda N t ^ 2 ≤ 12000000 := by
    nlinarith
  exact one_div_le_one_div_of_le hdenPos hden

/-- The exact weighted middle block is uniformly bounded near one.  No
asymptotic notation or hidden conductor convention occurs in this statement.
-/
theorem norm_fordShiftedWeightedBlock_zero_le_middle
    {sigma t : ℝ} {N R : ℕ}
    (hsigma : 0 ≤ sigma)
    (hsigmaNear : 1 - 1 / 12000000 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      fordQualitativeCoefficient := by
  have hNOne : 1 < N := by omega
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ)).trans_le hNt
  have hsave := one_div_twelveMillion_le_fordSaving
    hNOne ht hNt htN
  have hexponent :
      1 - sigma - 1 / (3000000 * fordLambda N t ^ 2) ≤ 0 := by
    linarith
  have hNPos : 0 < N := by omega
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hraw := norm_fordShiftedWeightedBlock_zero_le_general
    ford_exponential_sum_qualitative fordQualitativeCoefficient_nonneg
    hsigma hNPos hNt hNR hR
  have hweight : ((N + 1 : ℕ) : ℝ) ^ (-sigma) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast (show N ≤ N + 1 by omega)
    · linarith
  have hmajorantNonneg : 0 ≤ fordGeneralMajorant
      fordQualitativeCoefficient 3000000 N t := by
    unfold fordGeneralMajorant
    exact mul_nonneg fordQualitativeCoefficient_nonneg
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)) _)
  have hcombine :
      (N : ℝ) ^ (-sigma) *
          fordGeneralMajorant fordQualitativeCoefficient 3000000 N t =
        fordQualitativeCoefficient * (N : ℝ) ^
          (1 - sigma - 1 / (3000000 * fordLambda N t ^ 2)) := by
    unfold fordGeneralMajorant
    calc
      (N : ℝ) ^ (-sigma) *
          (fordQualitativeCoefficient * (N : ℝ) ^
            (1 - 1 / (3000000 * fordLambda N t ^ 2))) =
          fordQualitativeCoefficient *
            ((N : ℝ) ^ (-sigma) * (N : ℝ) ^
              (1 - 1 / (3000000 * fordLambda N t ^ 2))) := by ring
      _ = fordQualitativeCoefficient * (N : ℝ) ^
          (-sigma + (1 - 1 / (3000000 * fordLambda N t ^ 2))) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      _ = fordQualitativeCoefficient * (N : ℝ) ^
          (1 - sigma - 1 / (3000000 * fordLambda N t ^ 2)) := by
        congr 2
        ring
  have hpow : (N : ℝ) ^
      (1 - sigma - 1 / (3000000 * fordLambda N t ^ 2)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hNReal hexponent
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          fordGeneralMajorant fordQualitativeCoefficient 3000000 N t := by
      simpa only [Nat.cast_add, Nat.cast_one] using hraw
    _ ≤ (N : ℝ) ^ (-sigma) *
          fordGeneralMajorant fordQualitativeCoefficient 3000000 N t :=
      mul_le_mul_of_nonneg_right hweight hmajorantNonneg
    _ = fordQualitativeCoefficient * (N : ℝ) ^
          (1 - sigma - 1 / (3000000 * fordLambda N t ^ 2)) := hcombine
    _ ≤ fordQualitativeCoefficient * 1 :=
      mul_le_mul_of_nonneg_left hpow fordQualitativeCoefficient_nonneg
    _ = fordQualitativeCoefficient := mul_one _

#print axioms fordLambda_le_two_of_le_sq
#print axioms one_div_twelveMillion_le_fordSaving
#print axioms norm_fordShiftedWeightedBlock_zero_le_middle

end

end GafniTao
