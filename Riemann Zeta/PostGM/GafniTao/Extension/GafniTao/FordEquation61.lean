import GafniTao.FordLemma51Shift

/-!
# Ford's equation (6.1)

This file records the exact one-parameter Weyl shift used at the entrance to
Ford's Lemma 6.3.  The endpoint convention is the source convention
`N < n <= R`; after translation the common interval is `N < n <= R-1`.
The two boundary losses are retained as `N/M + M`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The inner logarithmic sum `T(n)` in Ford's equation (6.7). -/
def fordLemma63T (M n : ℕ) (u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    fordLogOscillation t ((m : ℝ) / ((n : ℝ) + u))

/-- The common translated average occurring before equation (6.1). -/
def fordEquation61Average (M N R : ℕ) (u t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    ∑ n ∈ Finset.Ioc N (R - 1), fordShiftedLogPhase (n + m) u t

private theorem ford_sum_twice_Icc_one (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (2 * (m : ℝ))) =
      (M : ℝ) * (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      push_cast
      ring

/-- Exact factorization of the common average into the original phase and
the source inner sum `T(n)`. -/
theorem fordEquation61Average_eq
    {M N R : ℕ} {u t : ℝ} (hu : 0 < u) :
    fordEquation61Average M N R u t =
      ∑ n ∈ Finset.Ioc N (R - 1),
        fordShiftedLogPhase n u t * fordLemma63T M n u t := by
  unfold fordEquation61Average fordLemma63T
  simp_rw [fordShiftedLogPhase_add_factor _ _ hu]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Averaging over all `1 <= m <= M` loses at most `M(M+1)` unit-modulus
boundary terms before division by `M`. -/
theorem norm_fordEquation61_discrepancy_le
    {M N R : ℕ} {u t : ℝ} :
    ‖((((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t) -
        fordEquation61Average M N R u t)‖ ≤
      (M : ℝ) * (M + 1) := by
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
    _ ≤ ∑ m ∈ Finset.Icc 1 M, (2 * (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_fordShiftedExponentialSum_sub_common_shift_le
        (Finset.mem_Icc.mp hm).1
    _ = (M : ℝ) * (M + 1) := by
      exact ford_sum_twice_Icc_one M

/-- Ford's equation (6.1), pointwise in the shift and right endpoint.  Its
right-hand moment interval is enlarged to the literal source interval
`N < n <= 2N-1` only after taking norms. -/
theorem ford_equation_6_1
    {M N R : ℕ} {u t : ℝ}
    (hM : 1 ≤ M) (hMN : M ≤ N) (hR : R ≤ 2 * N) (hu : 0 < u) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (1 / (M : ℝ)) *
          (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) +
        (N : ℝ) / M + M := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hdisc := norm_fordEquation61_discrepancy_le
    (M := M) (N := N) (R := R) (u := u) (t := t)
  have htri :
      (M : ℝ) * ‖fordShiftedExponentialSum N R u t‖ ≤
        ‖fordEquation61Average M N R u t‖ + (M : ℝ) * (M + 1) := by
    have hnorm :
        ‖(((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t)‖ =
          (M : ℝ) * ‖fordShiftedExponentialSum N R u t‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
      positivity
    calc
      (M : ℝ) * ‖fordShiftedExponentialSum N R u t‖ =
          ‖(((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t)‖ := hnorm.symm
      _ ≤ ‖(((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t -
            fordEquation61Average M N R u t)‖ +
          ‖fordEquation61Average M N R u t‖ := by
        calc
          _ = ‖((((M : ℝ) : ℂ) * fordShiftedExponentialSum N R u t -
              fordEquation61Average M N R u t) +
                fordEquation61Average M N R u t)‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      _ ≤ ‖fordEquation61Average M N R u t‖ +
          (M : ℝ) * (M + 1) := by linarith
  have haverage :
      ‖fordEquation61Average M N R u t‖ ≤
        ∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖ := by
    rw [fordEquation61Average_eq hu]
    calc
      ‖∑ n ∈ Finset.Ioc N (R - 1),
          fordShiftedLogPhase n u t * fordLemma63T M n u t‖ ≤
        ∑ n ∈ Finset.Ioc N (R - 1),
          ‖fordShiftedLogPhase n u t * fordLemma63T M n u t‖ :=
            norm_sum_le _ _
      _ = ∑ n ∈ Finset.Ioc N (R - 1), ‖fordLemma63T M n u t‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, norm_fordShiftedLogPhase, one_mul]
      _ ≤ ∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          simp only [Finset.mem_Ioc] at hn ⊢
          omega
        · intro n hn _hnBig
          exact norm_nonneg _
  have hraw :
      (M : ℝ) * ‖fordShiftedExponentialSum N R u t‖ ≤
        (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) +
          (M : ℝ) * (M + 1) := htri.trans (by linarith)
  have hdivide :
      ‖fordShiftedExponentialSum N R u t‖ ≤
        (1 / (M : ℝ)) *
            (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) +
          (M + 1 : ℝ) := by
    apply (le_of_mul_le_mul_left ?_ hMpos)
    calc
      (M : ℝ) * ‖fordShiftedExponentialSum N R u t‖ ≤ _ := hraw
      _ = (M : ℝ) *
          ((1 / (M : ℝ)) *
              (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) +
            (M + 1 : ℝ)) := by field_simp
  have hone : (1 : ℝ) ≤ (N : ℝ) / M := by
    apply (le_div_iff₀ hMpos).2
    have hMNreal : (M : ℝ) ≤ N := by exact_mod_cast hMN
    simpa using hMNreal
  linarith

#print axioms fordEquation61Average_eq
#print axioms norm_fordEquation61_discrepancy_le
#print axioms ford_equation_6_1

end

end GafniTao
