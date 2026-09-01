import GafniTao.FordLemma51Shift

/-!
# Ford Lemma 5.1: averaging and selection of the physical scale

This file completes the first finite part of Ford's argument.  It averages
the translated blocks over `1 <= a <= M₁` and `b in B`, factors the common
`n`-sum, and selects an actual `z = n+u` in `[N,2N]`.  The empty common
interval is handled separately, so no maximum of an empty set is used.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The logarithmic double sum before the Taylor replacement in (5.2). -/
def fordLemma51LogU
    (M₁ : ℕ) (B : Finset ℕ) (t z : ℝ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
    fordLogOscillation t (((a * b : ℕ) : ℝ) / z)

/-- Ford's common translated average over `a` and `b`. -/
def fordLemma51CommonShiftAverage
    (M₁ : ℕ) (B : Finset ℕ) (N R : ℕ) (u t : ℝ) : ℂ :=
  ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
    ∑ n ∈ Finset.Ioc N (R - 1),
      fordShiftedLogPhase (n + a * b) u t

/-- Exact factorization of the common translated average. -/
theorem fordLemma51CommonShiftAverage_eq
    {M₁ N R : ℕ} {B : Finset ℕ} {u t : ℝ} (hu : 0 < u) :
    fordLemma51CommonShiftAverage M₁ B N R u t =
      ∑ n ∈ Finset.Ioc N (R - 1),
        fordShiftedLogPhase n u t *
          fordLemma51LogU M₁ B t ((n : ℝ) + u) := by
  unfold fordLemma51CommonShiftAverage fordLemma51LogU
  simp_rw [fordShiftedLogPhase_add_factor _ _ hu]
  simp_rw [Finset.mul_sum]
  calc
    (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
        ∑ n ∈ Finset.Ioc N (R - 1),
          fordShiftedLogPhase n u t *
            fordLogOscillation t (((a * b : ℕ) : ℝ) / ((n : ℝ) + u))) =
      ∑ a ∈ Finset.Icc 1 M₁, ∑ n ∈ Finset.Ioc N (R - 1), ∑ b ∈ B,
          fordShiftedLogPhase n u t *
            fordLogOscillation t (((a * b : ℕ) : ℝ) / ((n : ℝ) + u)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Ioc N (R - 1), ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordShiftedLogPhase n u t *
            fordLogOscillation t (((a * b : ℕ) : ℝ) / ((n : ℝ) + u)) := by
        rw [Finset.sum_comm]

/-- The averaged boundary discrepancy is bounded before division by the
literal number `M₁*|B|` of shifts. -/
theorem norm_fordLemma51_average_discrepancy_le
    {M₁ M₂ N R : ℕ} {B : Finset ℕ} {u t : ℝ}
    (hM₁ : 1 ≤ M₁) (hBpos : ∀ b ∈ B, 1 ≤ b)
    (hB : ∀ b ∈ B, b ≤ M₂) :
    ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
          fordShiftedExponentialSum N R u t) -
        fordLemma51CommonShiftAverage M₁ B N R u t‖ ≤
      ((M₁ * B.card : ℕ) : ℝ) *
        (2 * (M₁ : ℝ) * (M₂ : ℝ)) := by
  have hscalar :
      ((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
          fordShiftedExponentialSum N R u t) =
        ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordShiftedExponentialSum N R u t := by
    rw [Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul, Nat.card_Icc]
    push_cast
    ring
  rw [hscalar]
  unfold fordLemma51CommonShiftAverage
  simp_rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
        (fordShiftedExponentialSum N R u t -
          ∑ n ∈ Finset.Ioc N (R - 1),
            fordShiftedLogPhase (n + a * b) u t)‖ ≤
      ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
        ‖fordShiftedExponentialSum N R u t -
          ∑ n ∈ Finset.Ioc N (R - 1),
            fordShiftedLogPhase (n + a * b) u t‖ := by
      calc
        _ ≤ ∑ a ∈ Finset.Icc 1 M₁,
            ‖∑ b ∈ B, (fordShiftedExponentialSum N R u t -
              ∑ n ∈ Finset.Ioc N (R - 1),
                fordShiftedLogPhase (n + a * b) u t)‖ := norm_sum_le _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro a ha
          exact norm_sum_le _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
        (2 * (M₁ : ℝ) * (M₂ : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have ha' := Finset.mem_Icc.mp ha
      have hq : 1 ≤ a * b := Nat.mul_pos ha'.1 (hBpos b hb)
      calc
        ‖fordShiftedExponentialSum N R u t -
            ∑ n ∈ Finset.Ioc N (R - 1),
              fordShiftedLogPhase (n + a * b) u t‖ ≤
            2 * ((a * b : ℕ) : ℝ) :=
          norm_fordShiftedExponentialSum_sub_common_shift_le hq
        _ = 2 * (a : ℝ) * (b : ℝ) := by push_cast; ring
        _ ≤ 2 * (M₁ : ℝ) * (M₂ : ℝ) := by
          have haR : (a : ℝ) ≤ M₁ := by exact_mod_cast ha'.2
          have hbR : (b : ℝ) ≤ M₂ := by exact_mod_cast hB b hb
          have ha0 : (0 : ℝ) ≤ a := by positivity
          have hb0 : (0 : ℝ) ≤ b := by positivity
          have hM0 : (0 : ℝ) ≤ M₁ := by positivity
          nlinarith [mul_le_mul haR hbR hb0 hM0]
    _ = ((M₁ * B.card : ℕ) : ℝ) *
        (2 * (M₁ : ℝ) * (M₂ : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      push_cast
      ring

/-- After division by the nonzero number of shifts, the boundary loss is
the source term `2*M₁*M₂`. -/
theorem norm_fordShiftedExponentialSum_le_average
    {M₁ M₂ N R : ℕ} {B : Finset ℕ} {u t : ℝ}
    (hM₁ : 1 ≤ M₁) (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hB : ∀ b ∈ B, b ≤ M₂) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ /
          ((M₁ : ℝ) * B.card) +
        2 * (M₁ : ℝ) * (M₂ : ℝ) := by
  have hc : 0 < (M₁ : ℝ) * (B.card : ℝ) := by
    positivity
  have hdisc := norm_fordLemma51_average_discrepancy_le
    hM₁ hBpos hB (N := N) (R := R) (u := u) (t := t)
  have htri :
      ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
          fordShiftedExponentialSum N R u t)‖ ≤
        ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
            fordShiftedExponentialSum N R u t) -
          fordLemma51CommonShiftAverage M₁ B N R u t‖ +
        ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ := by
    calc
      _ = ‖(((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
            fordShiftedExponentialSum N R u t) -
          fordLemma51CommonShiftAverage M₁ B N R u t) +
          fordLemma51CommonShiftAverage M₁ B N R u t‖ := by
            rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have hnorm :
      ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
          fordShiftedExponentialSum N R u t)‖ =
        ((M₁ : ℝ) * B.card) *
          ‖fordShiftedExponentialSum N R u t‖ := by
    rw [norm_mul]
    have hscalarNorm :
        ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ))‖ =
          (M₁ : ℝ) * (B.card : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg]
      · push_cast
        ring
      · positivity
    rw [hscalarNorm]
  have hdisc' :
      ‖((((M₁ * B.card : ℕ) : ℝ) : ℂ) *
          fordShiftedExponentialSum N R u t) -
        fordLemma51CommonShiftAverage M₁ B N R u t‖ ≤
      ((M₁ : ℝ) * B.card) *
        (2 * (M₁ : ℝ) * (M₂ : ℝ)) := by
    simpa only [Nat.cast_mul] using hdisc
  have hmul :
      (M₁ : ℝ) * B.card * ‖fordShiftedExponentialSum N R u t‖ ≤
        ((M₁ : ℝ) * B.card) *
            (2 * (M₁ : ℝ) * (M₂ : ℝ)) +
          ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ := by
    rw [hnorm] at htri
    nlinarith
  rw [show ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ /
        ((M₁ : ℝ) * B.card) + 2 * (M₁ : ℝ) * (M₂ : ℝ) =
      (‖fordLemma51CommonShiftAverage M₁ B N R u t‖ +
        ((M₁ : ℝ) * B.card) * (2 * (M₁ : ℝ) * (M₂ : ℝ))) /
          ((M₁ : ℝ) * B.card) by field_simp]
  apply (le_div_iff₀ hc).2
  simpa [mul_comm, add_comm] using hmul

/-- A literal physical `z in [N,2N]` controls the common average. -/
theorem exists_fordLemma51LogU_controls_average
    {M₁ N R : ℕ} {B : Finset ℕ} {u t : ℝ}
    (hN : 0 < N) (hR : R ≤ 2 * N) (hu : 0 < u) (huOne : u ≤ 1) :
    ∃ z : ℝ, z ∈ Set.Icc (N : ℝ) (2 * N : ℝ) ∧
      ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ ≤
        (N : ℝ) * ‖fordLemma51LogU M₁ B t z‖ := by
  let C := Finset.Ioc N (R - 1)
  by_cases hC : C.Nonempty
  · obtain ⟨n, hn, hnmax⟩ := Finset.exists_max_image C
      (fun n => ‖fordLemma51LogU M₁ B t ((n : ℝ) + u)‖) hC
    refine ⟨(n : ℝ) + u, ?_, ?_⟩
    · have hn' := Finset.mem_Ioc.mp hn
      constructor
      · have hnR : (N : ℝ) < n := by exact_mod_cast hn'.1
        linarith
      · have hnR : (n : ℝ) + u ≤ R := by
          have hnR' : (n : ℝ) ≤ ((R - 1 : ℕ) : ℝ) := by
            exact_mod_cast hn'.2
          have hsub : (R - 1 : ℕ) + 1 = R := by omega
          have hcast : ((R - 1 : ℕ) : ℝ) + 1 = R := by
            exact_mod_cast hsub
          linarith
        exact hnR.trans (by exact_mod_cast hR)
    · rw [fordLemma51CommonShiftAverage_eq hu]
      calc
        ‖∑ m ∈ C, fordShiftedLogPhase m u t *
            fordLemma51LogU M₁ B t ((m : ℝ) + u)‖ ≤
          ∑ m ∈ C, ‖fordShiftedLogPhase m u t *
            fordLemma51LogU M₁ B t ((m : ℝ) + u)‖ := norm_sum_le _ _
        _ = ∑ m ∈ C, ‖fordLemma51LogU M₁ B t ((m : ℝ) + u)‖ := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [norm_mul, norm_fordShiftedLogPhase, one_mul]
        _ ≤ ∑ _m ∈ C, ‖fordLemma51LogU M₁ B t ((n : ℝ) + u)‖ := by
          apply Finset.sum_le_sum
          intro m hm
          exact hnmax m hm
        _ = C.card * ‖fordLemma51LogU M₁ B t ((n : ℝ) + u)‖ := by
          simp
        _ ≤ (N : ℝ) * ‖fordLemma51LogU M₁ B t ((n : ℝ) + u)‖ := by
          gcongr
          rw [Nat.card_Ioc]
          omega
  · refine ⟨(N : ℝ), ?_, ?_⟩
    · constructor
      · exact le_rfl
      · norm_cast
        omega
    · rw [fordLemma51CommonShiftAverage_eq hu]
      have hCempty : Finset.Ioc N (R - 1) = ∅ := by
        exact Finset.not_nonempty_iff_eq_empty.mp hC
      simp [hCempty]
      exact mul_nonneg (Nat.cast_nonneg N)
        (norm_nonneg (fordLemma51LogU M₁ B t (N : ℝ)))

#print axioms fordLemma51CommonShiftAverage_eq
#print axioms norm_fordLemma51_average_discrepancy_le
#print axioms norm_fordShiftedExponentialSum_le_average
#print axioms exists_fordLemma51LogU_controls_average

end

end GafniTao
