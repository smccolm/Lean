import GafniTao.FordEquation61

/-!
# Ford's equation (6.1) at a real shift length

Ford declares the Weyl-shift length `M` to be real, while the inner sum is
over the integers `1 <= m <= M`.  This file makes that convention literal:
the finite sum uses `floor M`, but the averaging denominator and the two
source boundary terms retain the real value `M`.  The exact `2m-1` endpoint
count is what makes the source loss `N/M + M` survive flooring without an
extra constant.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

private theorem ford_sum_odd_Icc_one (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (2 * (m : ℝ) - 1)) = (M : ℝ) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      push_cast
      ring

/-- The exact natural-cutoff discrepancy is `M^2`, rather than the convenient
but lossy `M(M+1)` bound used by the earlier integer-only interface. -/
theorem norm_fordEquation61_discrepancy_le_sq
    {M N R : ℕ} {u t : ℝ} (hR : 1 ≤ R) :
    ‖((((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
        fordEquation61Average M N R u t)‖ ≤ (M : ℝ) ^ 2 := by
  have hscalar :
      (((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) =
        ∑ m ∈ Finset.Icc 1 M, fordShiftedExponentialSum N R u t := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul, Nat.card_Icc]
    push_cast
    ring
  rw [hscalar]
  unfold fordEquation61Average
  simp_rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (fordShiftedExponentialSum N R u t -
          ∑ n ∈ Finset.Ioc N (R - 1),
            fordShiftedLogPhase (n + m) u t)‖ ≤
      ∑ m ∈ Finset.Icc 1 M,
        ‖fordShiftedExponentialSum N R u t -
          ∑ n ∈ Finset.Ioc N (R - 1),
            fordShiftedLogPhase (n + m) u t‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (2 * (m : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_fordShiftedExponentialSum_sub_common_shift_le_sharp
        hR (Finset.mem_Icc.mp hm).1
    _ = (M : ℝ) ^ 2 := ford_sum_odd_Icc_one M

/-- Real-cutoff version of Ford's equation (6.1).  The actual finite inner
sum is cut off at `floor P`; all displayed scale factors are the source's
real `P`. -/
theorem ford_equation_6_1_real_cutoff
    {P : ℝ} {N R : ℕ} {u t : ℝ}
    (hP : 1 ≤ P) (hN : 1 ≤ N)
    (hRlower : N < R) (hR : R ≤ 2 * N) (hu : 0 < u) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (1 / P) *
          (∑ n ∈ Finset.Ioc N (2 * N - 1),
            ‖fordLemma63T ⌊P⌋₊ n u t‖) +
        (N : ℝ) / P + P := by
  let Q : ℕ := ⌊P⌋₊
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Nat.floor_pos.mpr hP
  have hQreal : (Q : ℝ) ≤ P := by
    dsimp [Q]
    exact Nat.floor_le hPpos.le
  have hQlt : P < (Q : ℝ) + 1 := by
    dsimp [Q]
    exact Nat.lt_floor_add_one P
  have hQnonneg : 0 ≤ P - Q := by linarith
  have hQgap : P - Q ≤ 1 := by linarith
  have hRpos : 1 ≤ R := by omega
  have hdisc := norm_fordEquation61_discrepancy_le_sq
    (M := Q) (N := N) (R := R) (u := u) (t := t) hRpos
  have hsumNorm := norm_fordShiftedExponentialSum_le_N hR u t
  have hrealDisc :
      ‖((P : ℂ) * fordShiftedExponentialSum N R u t) -
          fordEquation61Average Q N R u t‖ ≤
        (P - Q) * (N : ℝ) + (Q : ℝ) ^ 2 := by
    have hsplit :
        ((P : ℂ) * fordShiftedExponentialSum N R u t) -
            fordEquation61Average Q N R u t =
          (((P - Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) +
            ((((Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
              fordEquation61Average Q N R u t) := by
      push_cast
      ring
    rw [hsplit]
    calc
      ‖(((P - Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) +
          ((((Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
            fordEquation61Average Q N R u t)‖ ≤
        ‖((P - Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t‖ +
          ‖((((Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
            fordEquation61Average Q N R u t)‖ := norm_add_le _ _
      _ = (P - Q) * ‖fordShiftedExponentialSum N R u t‖ +
          ‖((((Q : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
            fordEquation61Average Q N R u t)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hQnonneg]
      _ ≤ (P - Q) * (N : ℝ) + (Q : ℝ) ^ 2 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hsumNorm hQnonneg) hdisc
  have htri :
      P * ‖fordShiftedExponentialSum N R u t‖ ≤
        ‖fordEquation61Average Q N R u t‖ +
          ((P - Q) * (N : ℝ) + (Q : ℝ) ^ 2) := by
    have hnorm :
        ‖(P : ℂ) * fordShiftedExponentialSum N R u t‖ =
          P * ‖fordShiftedExponentialSum N R u t‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hPpos.le]
    calc
      P * ‖fordShiftedExponentialSum N R u t‖ =
          ‖(P : ℂ) * fordShiftedExponentialSum N R u t‖ := hnorm.symm
      _ ≤ ‖(P : ℂ) * fordShiftedExponentialSum N R u t -
            fordEquation61Average Q N R u t‖ +
          ‖fordEquation61Average Q N R u t‖ := by
        calc
          _ = ‖((P : ℂ) * fordShiftedExponentialSum N R u t -
              fordEquation61Average Q N R u t) +
                fordEquation61Average Q N R u t‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ ≤ ‖fordEquation61Average Q N R u t‖ +
          ((P - Q) * (N : ℝ) + (Q : ℝ) ^ 2) := by linarith
  have haverage :
      ‖fordEquation61Average Q N R u t‖ ≤
        ∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T Q n u t‖ := by
    rw [fordEquation61Average_eq hu]
    calc
      ‖∑ n ∈ Finset.Ioc N (R - 1),
          fordShiftedLogPhase n u t * fordLemma63T Q n u t‖ ≤
        ∑ n ∈ Finset.Ioc N (R - 1),
          ‖fordShiftedLogPhase n u t * fordLemma63T Q n u t‖ :=
            norm_sum_le _ _
      _ = ∑ n ∈ Finset.Ioc N (R - 1), ‖fordLemma63T Q n u t‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, norm_fordShiftedLogPhase, one_mul]
      _ ≤ ∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T Q n u t‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_Ioc] at hn ⊢
          omega
        · intro n hn _hnBig
          exact norm_nonneg _
  have hraw :
      P * ‖fordShiftedExponentialSum N R u t‖ ≤
        (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T Q n u t‖) +
          (N : ℝ) + P ^ 2 := by
    calc
      P * ‖fordShiftedExponentialSum N R u t‖ ≤
          ‖fordEquation61Average Q N R u t‖ +
            ((P - Q) * (N : ℝ) + (Q : ℝ) ^ 2) := htri
      _ ≤ (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T Q n u t‖) +
            ((P - Q) * (N : ℝ) + (Q : ℝ) ^ 2) := by gcongr
      _ ≤ (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T Q n u t‖) +
          (N : ℝ) + P ^ 2 := by
        have hgapN : (P - Q) * (N : ℝ) ≤ N := by
          have hN0 : (0 : ℝ) ≤ N := by positivity
          nlinarith
        have hQsq : (Q : ℝ) ^ 2 ≤ P ^ 2 := by nlinarith
        linarith
  apply (le_of_mul_le_mul_left ?_ hPpos)
  calc
    P * ‖fordShiftedExponentialSum N R u t‖ ≤ _ := hraw
    _ = P * ((1 / P) *
          (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T ⌊P⌋₊ n u t‖) +
        (N : ℝ) / P + P) := by
      dsimp [Q]
      field_simp

#print axioms norm_fordEquation61_discrepancy_le_sq
#print axioms ford_equation_6_1_real_cutoff

end

end GafniTao
