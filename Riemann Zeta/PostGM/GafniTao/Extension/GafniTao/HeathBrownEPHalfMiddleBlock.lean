import GafniTao.FordShiftedWeylRange
import GafniTao.FordSmallLambdaB
import GafniTao.HeathBrownEPHalfMiddleExponent
import GafniTao.HeathBrownHybridZetaBlock
import GafniTao.HeathBrownHybridZetaLong

/-!
# The conductor-scale blocks in Heath--Brown's zeta estimate

This file keeps the two source estimates separate.  The B-process handles
`1 ≤ tau ≤ 9/5`; the shifted Weyl estimate handles `9/5 ≤ tau ≤ 2`.
Their weighted forms are then compared with the same zeta exponent.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The raw shifted-Weyl bound with its exact logarithmic-scale exponent on
the range between `9/5` and `2`. -/
theorem ford_shifted_weyl_below_square_lambda_power
    {N R : ℕ} {u tau : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (htauLow : 9 / 5 ≤ tau) (htauHigh : tau ≤ 2) :
    ‖fordShiftedExponentialSum N R u ((N : ℝ) ^ tau)‖ ≤
      90 * (N : ℝ) ^ (3 / 2 - tau / 3) := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hNOne : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have htauOne : (1 : ℝ) ≤ tau := by norm_num at htauLow ⊢; linarith
  have hNt : (N : ℝ) ≤ (N : ℝ) ^ tau := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNOne htauOne
  have htN : (N : ℝ) ^ tau ≤ (N : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hNOne htauHigh
  have hraw := ford_shifted_weyl_below_square
    hN hNR hR hu0 hu1 hNt htN
  let A : ℝ := (N + 1 : ℕ) + u
  let Y : ℝ := fordCubeRoot ((N : ℝ) ^ tau)
  let Z : ℝ := (N : ℝ) ^ (3 / 2 - tau / 3)
  have hAle : A ≤ 2 * (N : ℝ) := by
    dsimp [A]
    norm_num
    have hNTwo : (2 : ℝ) ≤ N := by
      exact_mod_cast (show 2 ≤ N by omega)
    linarith
  have hYeq : Y = (N : ℝ) ^ (tau / 3) := by
    dsimp only [Y]
    exact fordCubeRoot_rpow hNpos
  have hYpos : 0 < Y := by rw [hYeq]; positivity
  have hZpos : 0 < Z := by dsimp only [Z]; positivity
  have hZsq : Z ^ 2 = (N : ℝ) ^ (3 - 2 * tau / 3) := by
    dsimp only [Z]
    calc
      ((N : ℝ) ^ (3 / 2 - tau / 3)) ^ 2 =
          ((N : ℝ) ^ (3 / 2 - tau / 3)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((3 / 2 - tau / 3) * 2) :=
        (Real.rpow_mul hNpos.le _ _).symm
      _ = (N : ℝ) ^ (3 - 2 * tau / 3) := by ring_nf
  have hYsq : Y ^ 2 = (N : ℝ) ^ (2 * tau / 3) := by
    rw [hYeq]
    calc
      ((N : ℝ) ^ (tau / 3)) ^ 2 =
          ((N : ℝ) ^ (tau / 3)) ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = (N : ℝ) ^ ((tau / 3) * 2) :=
        (Real.rpow_mul hNpos.le _ _).symm
      _ = (N : ℝ) ^ (2 * tau / 3) := by ring_nf
  have hsplit : (N : ℝ) ^ 3 = Z ^ 2 * Y ^ 2 := by
    rw [← Real.rpow_natCast, hZsq, hYsq, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hYcube : Y ^ 3 = (N : ℝ) ^ tau := by
    dsimp only [Y]
    exact fordCubeRoot_cube (Real.rpow_pos_of_pos hNpos tau)
  have hinside :
      (4 * (N : ℝ) ^ 2 / ((N : ℝ) ^ tau)) * A * Y ≤
        9 * Z ^ 2 := by
    rw [← hYcube]
    rw [show (4 * (N : ℝ) ^ 2 / Y ^ 3) * A * Y =
      (4 * (N : ℝ) ^ 2 * A * Y) / Y ^ 3 by ring]
    rw [div_le_iff₀ (pow_pos hYpos 3)]
    have hleft : 4 * (N : ℝ) ^ 2 * A ≤ 8 * (N : ℝ) ^ 3 := by
      nlinarith [hAle, hNpos, sq_nonneg (N : ℝ)]
    have hbase : 4 * (N : ℝ) ^ 2 * A ≤ 9 * Z ^ 2 * Y ^ 2 := by
      calc
        4 * (N : ℝ) ^ 2 * A ≤ 8 * (N : ℝ) ^ 3 := hleft
        _ ≤ 9 * (N : ℝ) ^ 3 := by
          nlinarith [pow_nonneg hNpos.le 3]
        _ = 9 * Z ^ 2 * Y ^ 2 := by rw [hsplit]; ring
    have hmul := mul_le_mul_of_nonneg_right hbase hYpos.le
    nlinarith [sq_nonneg Y]
  have hsqrt :
      Real.sqrt
          ((4 * (N : ℝ) ^ 2 / ((N : ℝ) ^ tau)) * A * Y) ≤
        3 * Z := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrt' :
      Real.sqrt
          ((4 * (N : ℝ) ^ 2 / ((N : ℝ) ^ tau)) *
            ((N + 1 : ℕ) + u) *
              fordCubeRoot ((N : ℝ) ^ tau)) ≤
        3 * (N : ℝ) ^ (3 / 2 - tau / 3) := by
    simpa only [A, Y, Z] using hsqrt
  exact hraw.trans (by nlinarith)

/-- The B-process controls a weighted conductor-scale block on
`1 ≤ log t / log N ≤ 9/5` with the final Heath--Brown zeta exponent. -/
theorem norm_fordShiftedWeightedBlock_zero_le_middle_B_zeta
    {sigma t : ℝ} {N R : ℕ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaRange : 5 / 6 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (htauUpper : fordLambda N t ≤ 9 / 5)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      130 * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := by
  have hNOne : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by
    have hcast : (1024 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    norm_num at hcast ⊢
    linarith
  have ht : 0 < t := hNpos.trans_le hNt
  have htOne : 1 ≤ t := by
    exact (le_of_lt hNRealOne).trans hNt
  let tau := fordLambda N t
  let u := 1 - sigma
  have htauOne : 1 ≤ tau := by
    simpa only [tau] using one_le_fordLambda hNOne hNt
  have htauPos : 0 < tau := zero_lt_one.trans_le htauOne
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith
  have hu6 : u ≤ 1 / 6 := by dsimp only [u]; linarith
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
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (130 * Real.sqrt t) := by
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
  have hoptimized :
      1 / 2 - sigma / tau ≤
        heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) := by
    have := heathBrownHalf_middle_B_exponent_le
      hu0 hu6 htauOne (by simpa only [tau] using htauUpper)
    simpa only [u, sub_sub_cancel] using this
  have hpow :
      t ^ (1 / 2 - sigma / tau) ≤
        t ^ (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le htOne hoptimized
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (130 * Real.sqrt t) := hblock
    _ ≤ (N : ℝ) ^ (-sigma) * (130 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = 130 * (N : ℝ) ^ (tau / 2 - sigma) := hcombine
    _ = 130 * t ^ (1 / 2 - sigma / tau) := by rw [hscalePower]
    _ ≤ 130 * t ^ (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ)) := by
      gcongr
    _ = 130 * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := by rfl

/-- The shifted Weyl estimate controls a weighted conductor-scale block on
`9/5 ≤ log t / log N ≤ 2` with the final Heath--Brown zeta exponent. -/
theorem norm_fordShiftedWeightedBlock_zero_le_middle_Weyl_zeta
    {sigma t : ℝ} {N R : ℕ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaRange : 5 / 6 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (htauLower : 9 / 5 ≤ fordLambda N t)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      90 * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := by
  have hNOne : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by
    have hcast : (1024 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    norm_num at hcast ⊢
    linarith
  have ht : 0 < t := hNpos.trans_le hNt
  have htOne : 1 ≤ t := (le_of_lt hNRealOne).trans hNt
  let tau := fordLambda N t
  let u := 1 - sigma
  have htauLow : 9 / 5 ≤ tau := by
    simpa only [tau] using htauLower
  have htauPos : 0 < tau := by norm_num at htauLow ⊢; linarith
  have htauHigh : tau ≤ 2 := by
    simpa only [tau] using fordLambda_le_two_of_le_sq hNOne ht htN
  have hu0 : 0 ≤ u := by dsimp only [u]; linarith
  have hu6 : u ≤ 1 / 6 := by dsimp only [u]; linarith
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
  have hmajorant :
      0 ≤ 90 * (N : ℝ) ^ (3 / 2 - tau / 3) := by positivity
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
  have hoptimized :
      (u + 1 / 2) / tau - 1 / 3 ≤
        heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) :=
    heathBrownHalf_middle_Weyl_exponent_le hu0 hu6 htauLow
  have hpow :
      t ^ ((u + 1 / 2) / tau - 1 / 3) ≤
        t ^ (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le htOne hoptimized
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) := hblock
    _ ≤ (N : ℝ) ^ (-sigma) *
          (90 * (N : ℝ) ^ (3 / 2 - tau / 3)) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = 90 * (N : ℝ) ^ (u + 1 / 2 - tau / 3) := hcombine
    _ = 90 * t ^ ((u + 1 / 2) / tau - 1 / 3) := by
      rw [hscalePower]
    _ ≤ 90 * t ^ (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ)) := by
      gcongr
    _ = 90 * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := by rfl

/-- Complete conductor-scale block estimate.  The split at `tau = 9/5` is
internal and no qualitative Ford loss remains in the public conclusion. -/
theorem norm_fordShiftedWeightedBlock_zero_le_middle_zeta
    {sigma t : ℝ} {N R : ℕ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaRange : 5 / 6 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      130 * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := by
  by_cases htau : fordLambda N t ≤ 9 / 5
  · exact norm_fordShiftedWeightedBlock_zero_le_middle_B_zeta
      hsigmaUpper hsigmaRange hN hNt htN htau hNR hR
  · have hweyl := norm_fordShiftedWeightedBlock_zero_le_middle_Weyl_zeta
      hsigmaUpper hsigmaRange hN hNt htN (le_of_not_ge htau) hNR hR
    have hpow : 0 ≤ t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ)) := Real.rpow_nonneg (le_trans (by
          have : (0 : ℝ) ≤ N := by positivity
          exact this) hNt) _
    exact hweyl.trans (by nlinarith)

#print axioms ford_shifted_weyl_below_square_lambda_power
#print axioms norm_fordShiftedWeightedBlock_zero_le_middle_B_zeta
#print axioms norm_fordShiftedWeightedBlock_zero_le_middle_Weyl_zeta
#print axioms norm_fordShiftedWeightedBlock_zero_le_middle_zeta

end

end GafniTao
