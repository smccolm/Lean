import GafniTao.PintzNearOneZetaBlock
import GafniTao.HeathBrownEPHalfMiddleBlock

/-!
# Pintz's near-one estimate on conductor-scale blocks

For `1 <= log t / log N <= 2` and `sigma >= 11/12`, the exact B-process
and shifted-Weyl exponents are nonpositive.  We retain the source split at
`9/5` and prove the two weighted bounds directly from their prefix sums.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

private theorem pintz_nearOne_middle_B_exponent_nonpos
    {sigma tau : ℝ} (hsigma : 11 / 12 ≤ sigma)
    (htauPos : 0 < tau) (htau : tau ≤ 9 / 5) :
    1 / 2 - sigma / tau ≤ 0 := by
  rw [sub_nonpos]
  exact (le_div_iff₀ htauPos).2 (by nlinarith)

private theorem pintz_nearOne_middle_Weyl_exponent_nonpos
    {sigma tau : ℝ} (hsigmaLower : 11 / 12 ≤ sigma)
    (htau : 9 / 5 ≤ tau) :
    ((1 - sigma) + 1 / 2) / tau - 1 / 3 ≤ 0 := by
  have htauPos : 0 < tau := by linarith
  rw [sub_nonpos, div_le_iff₀ htauPos]
  nlinarith

/-- B-process branch of the conductor-scale estimate. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_B
    {epsilon sigma t : ℝ} {N R : ℕ}
    (hepsilon : 0 < epsilon) (hsigmaUpper : sigma ≤ 1)
    (hsigmaLower : 11 / 12 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (htauUpper : fordLambda N t ≤ 9 / 5)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      130 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  have hNOne : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by
    have hcast : (1024 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    norm_num at hcast ⊢
    linarith
  have ht : 0 < t := hNpos.trans_le hNt
  have htOne : 1 ≤ t := (le_of_lt hNRealOne).trans hNt
  let tau : ℝ := fordLambda N t
  have htauOne : 1 ≤ tau := by
    simpa only [tau] using one_le_fordLambda hNOne hNt
  have htauPos : 0 < tau := zero_lt_one.trans_le htauOne
  have hprefix : ∀ j : ℕ, j ≤ R - N →
      ‖∑ k ∈ Finset.range j,
          fordShiftedLogPhase (N + 1 + k) 0 t‖ ≤
        130 * Real.sqrt t := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
    · rw [← fordShiftedExponentialSum_eq_sum_range]
      exact ford_shifted_exponential_sum_B_process
        hN (by omega) (by omega) (by norm_num) (by norm_num) hNt htN
  have hblock :
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) * (130 * Real.sqrt t) := by
    unfold fordShiftedWeightedBlock
    simp only [add_zero]
    apply ford_norm_weighted_Ioc_le_of_antitone
        (fun n => (n : ℝ) ^ (-sigma))
        (fun n => fordShiftedLogPhase n 0 t) N R
        (130 * Real.sqrt t) hNR
    · intro n _hn
      positivity
    · intro n _hnN _hnR
      apply Real.rpow_le_rpow_of_nonpos
      · exact Nat.cast_pos.mpr (by omega)
      · exact Nat.cast_le.mpr (Nat.le_succ n)
      · linarith
    · exact hprefix
  have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos
    · exact Nat.cast_le.mpr (Nat.le_succ N)
    · linarith
  have hmajorant : 0 ≤ 130 * Real.sqrt t := by positivity
  have hsqrt : Real.sqrt t = (N : ℝ) ^ (tau / 2) := by
    rw [Real.sqrt_eq_rpow, ← rpow_fordLambda_eq hNOne ht]
    calc
      ((N : ℝ) ^ tau) ^ (1 / 2 : ℝ) =
          (N : ℝ) ^ (tau * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hNpos.le _ _).symm
      _ = (N : ℝ) ^ (tau / 2) := by ring_nf
  have hcombine :
      (N : ℝ) ^ (-sigma) * (130 * Real.sqrt t) =
        130 * (N : ℝ) ^ (tau / 2 - sigma) := by
    rw [hsqrt]
    calc
      (N : ℝ) ^ (-sigma) * (130 * (N : ℝ) ^ (tau / 2)) =
          130 * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ (tau / 2)) := by ring
      _ = 130 * (N : ℝ) ^ (-sigma + tau / 2) := by
        rw [← Real.rpow_add hNpos]
      _ = 130 * (N : ℝ) ^ (tau / 2 - sigma) := by ring
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNRealOne
  have htauLog : tau * Real.log (N : ℝ) = Real.log t := by
    dsimp only [tau, fordLambda]
    field_simp [hlogN.ne']
  have hscaleExponent :
      Real.log (N : ℝ) * (tau / 2 - sigma) =
        Real.log t * (1 / 2 - sigma / tau) := by
    rw [← htauLog]
    field_simp [htauPos.ne']
  have hscalePower :
      (N : ℝ) ^ (tau / 2 - sigma) =
        t ^ (1 / 2 - sigma / tau) := by
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos ht,
      hscaleExponent]
  have hnonpos : 1 / 2 - sigma / tau ≤ 0 :=
    pintz_nearOne_middle_B_exponent_nonpos hsigmaLower htauPos
      (by simpa only [tau] using htauUpper)
  have htarget : 0 ≤ (1 / 2 : ℝ) *
      (1 - sigma) ^ (3 / 2 : ℝ) + epsilon := by
    have : 0 ≤ 1 - sigma := by linarith
    positivity
  have hpow := Real.rpow_le_rpow_of_exponent_le htOne
    (hnonpos.trans htarget)
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) * (130 * Real.sqrt t) := hblock
    _ ≤ (N : ℝ) ^ (-sigma) * (130 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = 130 * (N : ℝ) ^ (tau / 2 - sigma) := hcombine
    _ = 130 * t ^ (1 / 2 - sigma / tau) := by rw [hscalePower]
    _ ≤ 130 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by gcongr

/-- Shifted-Weyl branch of the conductor-scale estimate. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_Weyl
    {epsilon sigma t : ℝ} {N R : ℕ}
    (hepsilon : 0 < epsilon) (hsigmaUpper : sigma ≤ 1)
    (hsigmaLower : 11 / 12 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (htauLower : 9 / 5 ≤ fordLambda N t)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      90 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  have hNOne : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by
    have hcast : (1024 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    norm_num at hcast ⊢
    linarith
  have ht : 0 < t := hNpos.trans_le hNt
  have htOne : 1 ≤ t := (le_of_lt hNRealOne).trans hNt
  let tau : ℝ := fordLambda N t
  let u : ℝ := 1 - sigma
  have htauLow : 9 / 5 ≤ tau := by simpa only [tau] using htauLower
  have htauPos : 0 < tau := by linarith
  have htauHigh : tau ≤ 2 := by
    simpa only [tau] using fordLambda_le_two_of_le_sq hNOne ht htN
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hteq : (N : ℝ) ^ tau = t := by
    simpa only [tau] using rpow_fordLambda_eq hNOne ht
  have hprefix : ∀ j : ℕ, j ≤ R - N →
      ‖∑ k ∈ Finset.range j,
          fordShiftedLogPhase (N + 1 + k) 0 t‖ ≤
        90 * (N : ℝ) ^ (3 / 2 - tau / 3) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
      exact Real.rpow_nonneg hNpos.le _
    · rw [← hteq]
      rw [← fordShiftedExponentialSum_eq_sum_range]
      exact ford_shifted_weyl_below_square_lambda_power
        hN (by omega) (by omega) (by norm_num) (by norm_num)
          htauLow htauHigh
  have hblock :
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) := by
    unfold fordShiftedWeightedBlock
    simp only [add_zero]
    apply ford_norm_weighted_Ioc_le_of_antitone
        (fun n => (n : ℝ) ^ (-sigma))
        (fun n => fordShiftedLogPhase n 0 t) N R
        (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) hNR
    · intro n _hn
      positivity
    · intro n _hnN _hnR
      apply Real.rpow_le_rpow_of_nonpos
      · exact Nat.cast_pos.mpr (by omega)
      · exact Nat.cast_le.mpr (Nat.le_succ n)
      · linarith
    · exact hprefix
  have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos
    · exact Nat.cast_le.mpr (Nat.le_succ N)
    · linarith
  have hmajorant : 0 ≤ 90 * (N : ℝ) ^ (3 / 2 - tau / 3) := by positivity
  have hcombine :
      (N : ℝ) ^ (-sigma) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) =
        90 * (N : ℝ) ^ (u + 1 / 2 - tau / 3) := by
    calc
      (N : ℝ) ^ (-sigma) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) =
          90 * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ (3 / 2 - tau / 3)) := by ring
      _ = 90 * (N : ℝ) ^ (-sigma + (3 / 2 - tau / 3)) := by
        rw [← Real.rpow_add hNpos]
      _ = 90 * (N : ℝ) ^ (u + 1 / 2 - tau / 3) := by
        dsimp only [u]
        ring
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNRealOne
  have htauLog : tau * Real.log (N : ℝ) = Real.log t := by
    dsimp only [tau, fordLambda]
    field_simp [hlogN.ne']
  have hscaleExponent :
      Real.log (N : ℝ) * (u + 1 / 2 - tau / 3) =
        Real.log t * ((u + 1 / 2) / tau - 1 / 3) := by
    rw [← htauLog]
    field_simp [htauPos.ne']
  have hscalePower :
      (N : ℝ) ^ (u + 1 / 2 - tau / 3) =
        t ^ ((u + 1 / 2) / tau - 1 / 3) := by
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos ht,
      hscaleExponent]
  have hnonpos : (u + 1 / 2) / tau - 1 / 3 ≤ 0 := by
    simpa only [u] using pintz_nearOne_middle_Weyl_exponent_nonpos
      hsigmaLower htauLow
  have htarget : 0 ≤ (1 / 2 : ℝ) *
      (1 - sigma) ^ (3 / 2 : ℝ) + epsilon := by positivity
  have hpow := Real.rpow_le_rpow_of_exponent_le htOne
    (hnonpos.trans htarget)
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) := hblock
    _ ≤ (N : ℝ) ^ (-sigma) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = 90 * (N : ℝ) ^ (u + 1 / 2 - tau / 3) := hcombine
    _ = 90 * t ^ ((u + 1 / 2) / tau - 1 / 3) := by rw [hscalePower]
    _ ≤ 90 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by gcongr

/-- Complete native conductor-scale block estimate for Pintz's strict
near-one segment. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle
    {epsilon sigma t : ℝ} {N R : ℕ}
    (hepsilon : 0 < epsilon) (hsigmaUpper : sigma ≤ 1)
    (hsigmaLower : 11 / 12 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      130 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  by_cases htau : fordLambda N t ≤ 9 / 5
  · exact norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_B
      hepsilon hsigmaUpper hsigmaLower hN hNt htN htau hNR hR
  · have hweyl :=
      norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_Weyl
        hepsilon hsigmaUpper hsigmaLower hN hNt htN
          (le_of_not_ge htau) hNR hR
    have hpow : 0 ≤ t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) :=
      Real.rpow_nonneg (by
        have hNpos : (0 : ℝ) ≤ N := by positivity
        exact hNpos.trans hNt) _
    exact hweyl.trans (by nlinarith)

#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_B
#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle_Weyl
#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne_middle

end

end GafniTao
