import GafniTao.FordQualitativeTheorem2
import GafniTao.FordFiniteZetaUnshifted
import GafniTao.FordCubicSourceBound

/-!
# Finite zeta sums from a general Ford estimate

The published Lemma-7.3 dyadic/Abel argument is independent of Ford's
optimized decimal constants.  These declarations expose that parameterized
consumer and then instantiate it with the proved qualitative estimate.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordGeneralMajorant (C D : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  C * (N : ℝ) ^ (1 - 1 / (D * fordLambda N t ^ 2))

def fordGeneralDyadicRawMajorant
    (C D sigma : ℝ) (j : ℕ) (u t : ℝ) : ℝ :=
  (((2 ^ j + 1 : ℕ) : ℝ) + u) ^ (-sigma) *
    fordGeneralMajorant C D (2 ^ j) t

theorem norm_fordShiftedWeightedBlock_le_general
    {C D sigma u t : ℝ} {N R : ℕ}
    (hFord : FordExponentialSumEstimate C D)
    (hsigma : 0 ≤ sigma) (hN : 0 < N) (hNt : (N : ℝ) ≤ t)
    (hu : 0 < u) (huOne : u ≤ 1) (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R u t‖ ≤
      (((N + 1 : ℕ) : ℝ) + u) ^ (-sigma) *
        fordGeneralMajorant C D N t := by
  apply norm_fordShiftedWeightedBlock_le hsigma hu hNR
  intro Q hNQ hQR
  exact hFord hN hNt hu huOne hNQ (hQR.trans hR)

theorem norm_fordGeneralDyadicWeightedShellSum_le_raw
    {C D sigma u t : ℝ} {r M : ℕ}
    (hFord : FordExponentialSumEstimate C D)
    (hC : 0 ≤ C)
    (hsigma : 0 ≤ sigma) (hu : 0 < u) (huOne : u ≤ 1)
    (hMt : (M : ℝ) ≤ t) :
    ‖fordDyadicWeightedShellSum sigma r M u t‖ ≤
      ∑ j ∈ Finset.range r,
        fordGeneralDyadicRawMajorant C D sigma j u t := by
  unfold fordDyadicWeightedShellSum
  calc
    ‖∑ j ∈ Finset.range r,
        fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) u t‖ ≤
      ∑ j ∈ Finset.range r,
        ‖fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) u t‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range r,
        fordGeneralDyadicRawMajorant C D sigma j u t := by
      apply Finset.sum_le_sum
      intro j _hj
      by_cases hNonempty : 2 ^ j < min M (2 ^ (j + 1))
      · have hNM : 2 ^ j ≤ M :=
          (Nat.le_of_lt hNonempty).trans (min_le_left _ _)
        have hNt : ((2 ^ j : ℕ) : ℝ) ≤ t :=
          (by exact_mod_cast hNM : ((2 ^ j : ℕ) : ℝ) ≤ M).trans hMt
        have hUpper : min M (2 ^ (j + 1)) ≤ 2 * 2 ^ j := by
          calc
            min M (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
            _ = 2 * 2 ^ j := by rw [pow_succ]; omega
        exact norm_fordShiftedWeightedBlock_le_general hFord hsigma
          (pow_pos (by omega) _) hNt hu huOne hNonempty hUpper
      · have hEmpty : Finset.Ioc (2 ^ j) (min M (2 ^ (j + 1))) = ∅ :=
          Finset.Ioc_eq_empty hNonempty
        rw [fordShiftedWeightedBlock, hEmpty, Finset.sum_empty, norm_zero]
        unfold fordGeneralDyadicRawMajorant fordGeneralMajorant
        positivity

theorem fordGeneralDyadicRawMajorant_le_source
    {C D sigma u t : ℝ} {j : ℕ}
    (hC : 0 ≤ C) (hsigma : 0 ≤ sigma) (hu : 0 < u)
    (ht : 1 < t) (hD : 0 < D) :
    fordGeneralDyadicRawMajorant C D sigma j u t ≤
      C * Real.exp (fordDyadicExponent D sigma t j) := by
  have hBase : 0 < (((2 ^ j : ℕ) : ℝ)) := by positivity
  have hWeight : ((((2 ^ j + 1 : ℕ) : ℝ) + u) ^ (-sigma)) ≤
      (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact hBase
    · norm_num
      linarith
    · linarith
  have hMajorantNonneg : 0 ≤ fordGeneralMajorant C D (2 ^ j) t := by
    unfold fordGeneralMajorant
    positivity
  calc
    fordGeneralDyadicRawMajorant C D sigma j u t ≤
        (((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
          fordGeneralMajorant C D (2 ^ j) t :=
      mul_le_mul_of_nonneg_right hWeight hMajorantNonneg
    _ = C * ((((2 ^ j : ℕ) : ℝ) ^ (-sigma)) *
        (((2 ^ j : ℕ) : ℝ) ^
          (1 - 1 / (D * fordLambda (2 ^ j) t ^ 2)))) := by
      unfold fordGeneralMajorant
      ring
    _ = C * Real.exp (fordDyadicExponent D sigma t j) := by
      rw [fordTheorem2_dyadic_power_eq_exp ht hD.ne']

theorem norm_fordGeneralDyadicWeightedShellSum_le_exponent
    {C D sigma u t : ℝ} {r M : ℕ}
    (hFord : FordExponentialSumEstimate C D) (hC : 0 ≤ C)
    (hD : 0 < D) (hsigma : 0 ≤ sigma) (hu : 0 < u) (huOne : u ≤ 1)
    (ht : 1 < t) (hMt : (M : ℝ) ≤ t) :
    ‖fordDyadicWeightedShellSum sigma r M u t‖ ≤
      C * ∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j) := by
  refine (norm_fordGeneralDyadicWeightedShellSum_le_raw hFord hC
    hsigma hu huOne hMt).trans ?_
  calc
    (∑ j ∈ Finset.range r,
        fordGeneralDyadicRawMajorant C D sigma j u t) ≤
      ∑ j ∈ Finset.range r,
        C * Real.exp (fordDyadicExponent D sigma t j) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact fordGeneralDyadicRawMajorant_le_source hC hsigma hu ht hD
    _ = C * ∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j) := by rw [Finset.mul_sum]

theorem norm_fordFiniteHurwitzSum_le_general
    {C D sigma u t : ℝ} {M r : ℕ}
    (hFord : FordExponentialSumEstimate C D) (hC : 0 ≤ C) (hD : 0 < D)
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 1 < t)
    (hMPos : 1 ≤ M) (hMt : (M : ℝ) ≤ t) (hMpow : M ≤ 2 ^ r) :
    ‖fordFiniteHurwitzSum sigma M u t‖ ≤
      1 + C *
        (t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * D ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  rw [fordFiniteHurwitzSum_eq_weighted hu,
    ford_sum_Icc_eq_first_add_dyadic sigma hMPos hMpow]
  have htriangle := norm_add_le
    (((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t)
    (fordDyadicWeightedShellSum sigma r M u t)
  have hfirst := norm_ford_first_weighted_term_le_one (t := t) hsigmaLower hu
  have hshell := norm_fordGeneralDyadicWeightedShellSum_le_exponent
    (r := r) (M := M) hFord hC hD hsigmaLower hu huOne ht hMt
  have hcubic := fordCubicExpSum_le_source hsigmaUpper hD ht r
  calc
    ‖((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t +
        fordDyadicWeightedShellSum sigma r M u t‖ ≤
      ‖((1 : ℝ) + u) ^ (-sigma) • fordShiftedLogPhase 1 u t‖ +
        ‖fordDyadicWeightedShellSum sigma r M u t‖ := htriangle
    _ ≤ 1 + C * ∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j) := add_le_add hfirst hshell
    _ ≤ 1 + C *
        (t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * D ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by gcongr

theorem norm_fordFiniteHurwitzSum_floor_le_general
    {C D sigma u t : ℝ}
    (hFord : FordExponentialSumEstimate C D) (hC : 0 ≤ C) (hD : 0 < D)
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 1 < t) :
    ‖fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) u t‖ ≤
      1 + C *
        (t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * D ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  exact norm_fordFiniteHurwitzSum_le_general hFord hC hD
    hsigmaLower hsigmaUpper hu huOne ht (fordFiniteEndpoint_pos ht)
      (fordFiniteEndpoint_le ht) (fordFiniteEndpoint_le_two_pow_shellCount t)

theorem norm_fordPartialSum_le_general
    {C D sigma t : ℝ}
    (hFord : FordExponentialSumEstimate C D) (hC : 0 ≤ C) (hD : 0 < D)
    (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1) (ht : 1 < t) :
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      1 + C *
        (t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * D ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  rw [← fordFiniteHurwitzSum_zero_eq_partialSum]
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsumLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma (fordFiniteEndpoint t) 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero
      (sigma := sigma) (t := t) (fordFiniteEndpoint t)).tendsto.comp huLim
  apply le_of_tendsto hsumLim.norm
  exact Filter.Eventually.of_forall fun k => by
    apply norm_fordFiniteHurwitzSum_floor_le_general hFord hC hD
      hsigmaLower hsigmaUpper
    · dsimp [u]
      positivity
    · dsimp [u]
      rw [div_le_one (by positivity)]
      norm_num
    · exact ht

theorem norm_fordPartialSum_le_qualitative
    {sigma t : ℝ} (hsigmaLower : 0 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 1 < t) :
    ‖∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      1 + fordQualitativeCoefficient *
        (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  exact norm_fordPartialSum_le_general ford_exponential_sum_qualitative
    fordQualitativeCoefficient_nonneg (by norm_num) hsigmaLower hsigmaUpper ht

#print axioms norm_fordShiftedWeightedBlock_le_general
#print axioms norm_fordFiniteHurwitzSum_le_general
#print axioms norm_fordPartialSum_le_general
#print axioms norm_fordPartialSum_le_qualitative

end

end GafniTao
