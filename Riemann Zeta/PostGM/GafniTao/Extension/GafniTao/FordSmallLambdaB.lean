import GafniTao.FordLargeLambdaSelection
import RiemannZeta.GuthMaynard.LogarithmicKernel

/-!
# The shifted logarithmic B-process in Ford's small-lambda range

This file proves the genuine shifted second-derivative estimate needed at the
bottom of Ford's Section 6.  Unlike the unshifted kernel in the frozen
foundation, Ford's Theorem 2 has a real shift `0 < u <= 1` and a terminally
truncated endpoint `R <= 2N`; both are retained here.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

def fordShiftedRealPhase (N n : ℕ) (u t : ℝ) : ℝ :=
  logarithmicPhase t ((N + 1 + n : ℕ) + u)

theorem fordShiftedLogPhase_eq_unitaryPhase
    (N n : ℕ) (u t : ℝ) :
    fordShiftedLogPhase (N + 1 + n) u t =
      unitaryPhase (fordShiftedRealPhase N n u t) := by
  unfold fordShiftedLogPhase fordShiftedRealPhase unitaryPhase logarithmicPhase
  push_cast
  congr 1
  ring

theorem fordShiftedRealPhase_secondDifference_bounds
    {N n : ℕ} {u t : ℝ} (hN : 2 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ht : 0 < t) (hn : n < N - 1) :
    t / (16 * (N : ℝ) ^ 2) ≤
        (fordShiftedRealPhase N (n + 2) u t -
          fordShiftedRealPhase N (n + 1) u t) -
        (fordShiftedRealPhase N (n + 1) u t -
          fordShiftedRealPhase N n u t) ∧
      (fordShiftedRealPhase N (n + 2) u t -
          fordShiftedRealPhase N (n + 1) u t) -
        (fordShiftedRealPhase N (n + 1) u t -
          fordShiftedRealPhase N n u t) ≤ t / (N : ℝ) ^ 2 := by
  let x : ℝ := (N + 1 + n : ℕ) + u
  have hNreal : 0 < (N : ℝ) := by positivity
  have hxPos : 0 < x := by
    dsimp [x]
    positivity
  obtain ⟨xi, hxi, hxiEq⟩ := second_order_mean_value
    (logarithmicPhase t)
    (fun y => -t / y)
    (fun y => t / y ^ 2) x
    (fun y hy => hasDerivAt_logarithmicPhase t (hxPos.trans_le hy.1).ne')
    (fun y hy => by
      have hyPos : 0 < y := hxPos.trans_le hy.1
      convert (hasDerivAt_inv hyPos.ne').const_mul (-t) using 1
      ring_nf)
  have hxiLower : (N : ℝ) ≤ xi := by
    calc
      (N : ℝ) ≤ x := by
        dsimp [x]
        push_cast
        have hn0 : (0 : ℝ) ≤ n := by positivity
        linarith
      _ ≤ xi := hxi.1.le
  have hnUpper : n + 3 ≤ 2 * N := by omega
  have hnUpperReal : ((n + 3 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hnUpper
  simp only [Nat.cast_add, Nat.cast_ofNat] at hnUpperReal
  have hxiUpper : xi ≤ 4 * (N : ℝ) := by
    have hxi' : xi < x + 2 := hxi.2
    dsimp [x] at hxi'
    push_cast at hxi'
    have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hxiPos : 0 < xi := lt_of_lt_of_le hNreal hxiLower
  have hlower : t / (16 * (N : ℝ) ^ 2) ≤ t / xi ^ 2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * (N : ℝ) ^ 2)
      (sq_pos_of_pos hxiPos)).2
    have hsq : xi ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hupper : t / xi ^ 2 ≤ t / (N : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hxiPos) (sq_pos_of_pos hNreal)).2
    have hsq : (N : ℝ) ^ 2 ≤ xi ^ 2 := by nlinarith
    nlinarith
  have hEq :
      t / xi ^ 2 =
        (fordShiftedRealPhase N (n + 2) u t -
          fordShiftedRealPhase N (n + 1) u t) -
        (fordShiftedRealPhase N (n + 1) u t -
          fordShiftedRealPhase N n u t) := by
    norm_num [x, fordShiftedRealPhase] at hxiEq ⊢
    rw [hxiEq]
    ring
  exact ⟨hlower.trans_eq hEq, hEq.symm.trans_le hupper⟩

def fordShiftedBMajorant (N L : ℕ) (t : ℝ) : ℝ :=
  (((L - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) / (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t / (16 * (N : ℝ) ^ 2)) +
      2 * (Real.sqrt (t / (16 * (N : ℝ) ^ 2)) /
        (t / (16 * (N : ℝ) ^ 2)) + 1))

theorem fordShiftedBMajorant_le
    {N L : ℕ} {t : ℝ} (hN : 1 ≤ N) (hL : L ≤ N)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    fordShiftedBMajorant N L t ≤ 130 * Real.sqrt t := by
  have hNreal : 0 < (N : ℝ) := by positivity
  have ht : 0 < t := lt_of_lt_of_le hNreal hNt
  let y := Real.sqrt t
  have hy : 0 < y := Real.sqrt_pos.2 ht
  have hySq : y ^ 2 = t := Real.sq_sqrt ht.le
  have hyLeN : y ≤ (N : ℝ) := by
    rw [← Real.sqrt_sq (le_of_lt hNreal)]
    exact Real.sqrt_le_sqrt htN
  have hNLeYSq : (N : ℝ) ≤ y ^ 2 := by simpa [hySq] using hNt
  have hpred : (((L - 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.sub_le L 1 |>.trans hL)
  have hfirst :
      (((L - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) /
          (2 * Real.pi) + 2) ≤ t / (N : ℝ) + 2 := by
    have htwoPi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hcore :
        (((L - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) /
            (2 * Real.pi)) ≤ t / (N : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
      field_simp [hNreal.ne']
      nlinarith
    linarith
  have hsqrtDenom : Real.sqrt (16 * (N : ℝ) ^ 2) = 4 * (N : ℝ) := by
    rw [show 16 * (N : ℝ) ^ 2 = (4 * (N : ℝ)) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have hsqrtLambda :
      Real.sqrt (t / (16 * (N : ℝ) ^ 2)) = y / (4 * (N : ℝ)) := by
    rw [Real.sqrt_div ht.le, hsqrtDenom]
  have hlambdaPos : 0 < t / (16 * (N : ℝ) ^ 2) := by positivity
  have hsecond :
      2 * Real.pi / Real.sqrt (t / (16 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (16 * (N : ℝ) ^ 2)) /
            (t / (16 * (N : ℝ) ^ 2)) + 1) ≤
        40 * (N : ℝ) / y + 2 := by
    rw [Real.sqrt_div_self', hsqrtLambda]
    field_simp [hy.ne', hNreal.ne']
    nlinarith [Real.pi_lt_four]
  have hmul := mul_le_mul hfirst hsecond (by positivity)
    (by positivity : 0 ≤ t / (N : ℝ) + 2)
  have htDiv : t / (N : ℝ) ≤ y := by
    rw [div_le_iff₀ hNreal]
    rw [← hySq]
    simpa [pow_two] using mul_le_mul_of_nonneg_left hyLeN hy.le
  have hNDiv : (N : ℝ) / y ≤ y := by
    rw [div_le_iff₀ hy]
    simpa [pow_two] using hNLeYSq
  have hyOne : 1 ≤ y := by nlinarith [hNLeYSq]
  have hexpand :
      (t / (N : ℝ) + 2) * (40 * (N : ℝ) / y + 2) =
        40 * y + 2 * (t / (N : ℝ)) +
          80 * ((N : ℝ) / y) + 4 := by
    field_simp [hNreal.ne', hy.ne']
    nlinarith [hySq]
  unfold fordShiftedBMajorant
  calc
    (((L - 1 : ℕ) : ℝ) * (t / (N : ℝ) ^ 2) /
          (2 * Real.pi) + 2) *
        (2 * Real.pi / Real.sqrt (t / (16 * (N : ℝ) ^ 2)) +
          2 * (Real.sqrt (t / (16 * (N : ℝ) ^ 2)) /
            (t / (16 * (N : ℝ) ^ 2)) + 1)) ≤
        (t / (N : ℝ) + 2) * (40 * (N : ℝ) / y + 2) := hmul
    _ = 40 * y + 2 * (t / (N : ℝ)) +
          80 * ((N : ℝ) / y) + 4 := hexpand
    _ ≤ 130 * y := by nlinarith

theorem ford_shifted_exponential_sum_B_process
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    ‖fordShiftedExponentialSum N R u t‖ ≤ 130 * Real.sqrt t := by
  let L := R - N
  have hLpos : 0 < L := by dsimp [L]; omega
  have hLle : L ≤ N := by dsimp [L]; omega
  have hNtwo : 2 ≤ N := by omega
  have ht : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < N) hNt
  have hB := vanDerCorput_B_process
    (fordShiftedRealPhase N · u t) (L - 1)
    (t / (16 * (N : ℝ) ^ 2)) (t / (N : ℝ) ^ 2)
    (by positivity)
    (fun n hn =>
      (fordShiftedRealPhase_secondDifference_bounds hNtwo hu0 hu1 ht
        (by omega)).1)
    (fun n hn =>
      (fordShiftedRealPhase_secondDifference_bounds hNtwo hu0 hu1 ht
        (by omega)).2)
  have hsum :
      ∑ n ∈ Finset.range L, unitaryPhase (fordShiftedRealPhase N n u t) =
        fordShiftedExponentialSum N R u t := by
    have hNRL : N + L = R := by dsimp [L]; omega
    calc
      ∑ n ∈ Finset.range L, unitaryPhase (fordShiftedRealPhase N n u t) =
          ∑ n ∈ Finset.range L, fordShiftedLogPhase (N + 1 + n) u t := by
            apply Finset.sum_congr rfl
            intro n _hn
            exact (fordShiftedLogPhase_eq_unitaryPhase N n u t).symm
      _ = fordShiftedExponentialSum N (N + L) u t :=
        (fordShiftedExponentialSum_eq_sum_range N L u t).symm
      _ = fordShiftedExponentialSum N R u t := by rw [hNRL]
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred, hsum] at hB
  exact hB.trans (fordShiftedBMajorant_le (by omega) hLle hNt htN)

#print axioms fordShiftedRealPhase_secondDifference_bounds
#print axioms fordShiftedBMajorant_le
#print axioms ford_shifted_exponential_sum_B_process

end

end GafniTao
