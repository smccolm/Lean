import GafniTao.FordLemma51W

/-!
# Ford Lemma 5.1: the initial Weyl-shift boundary term

This file formalizes the finite translation at the start of Ford's proof of
Lemma 5.1.  The common interval is the literal `N < n <= R - 1`; translating
it by `q = a*b` loses at most `2*q` unit-modulus summands.  This is the source
of the displayed `2*M₁*M₂` term and is kept independent of the later Taylor
and moment estimates.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A logarithmic phase translated by `q` factors into its unshifted phase
and Ford's exact logarithmic oscillation. -/
theorem fordShiftedLogPhase_add_factor
    (n q : ℕ) {u t : ℝ} (hu : 0 < u) :
    fordShiftedLogPhase (n + q) u t =
      fordShiftedLogPhase n u t *
        fordLogOscillation t ((q : ℝ) / ((n : ℝ) + u)) := by
  have hn : 0 < (n : ℝ) + u := by positivity
  have hq : 0 < 1 + (q : ℝ) / ((n : ℝ) + u) := by positivity
  have hfactor :
      ((n + q : ℕ) : ℝ) + u =
        ((n : ℝ) + u) * (1 + (q : ℝ) / ((n : ℝ) + u)) := by
    push_cast
    field_simp
    ring
  unfold fordShiftedLogPhase fordLogOscillation
  rw [hfactor, Real.log_mul hn.ne' hq.ne']
  rw [show -I * ((t * (Real.log ((n : ℝ) + u) +
      Real.log (1 + (q : ℝ) / ((n : ℝ) + u))) : ℝ) : ℂ) =
      -I * ((t * Real.log ((n : ℝ) + u) : ℝ) : ℂ) +
        I * ((-(t * Real.log
          (1 + (q : ℝ) / ((n : ℝ) + u))) : ℝ) : ℂ) by
    push_cast
    ring]
  exact Complex.exp_add _ _

/-- Translation of the common finite interval by a natural displacement. -/
theorem ford_sum_common_shift_eq_translated
    (f : ℕ → ℂ) (N R q : ℕ) :
    (∑ n ∈ Finset.Ioc N (R - 1), f (n + q)) =
      ∑ m ∈ Finset.Ioc (N + q) (R - 1 + q), f m := by
  apply Finset.sum_bij (fun n _hn => n + q)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  · intro n₁ hn₁ n₂ hn₂ h
    omega
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    refine ⟨m - q, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
  · intro n hn
    rfl

/-- The left discrepancy after translating `(N,R]` by a positive `q` lies
inside an interval of exactly `q` integers. -/
theorem ford_Ioc_sdiff_shifted_subset_left
    {N R q : ℕ} (hq : 1 ≤ q) :
    Finset.Ioc N R \ Finset.Ioc (N + q) (R - 1 + q) ⊆
      Finset.Ioc N (N + q) := by
  intro m hm
  rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hm
  rw [Finset.mem_Ioc]
  rcases hm with ⟨⟨hNm, hmR⟩, hmNot⟩
  refine ⟨hNm, ?_⟩
  by_contra hmUpper
  apply hmNot
  constructor
  · omega
  · omega

/-- The right discrepancy after translating `(N,R]` by a positive `q` lies
inside the terminal interval of length `q-1`. -/
theorem ford_shifted_Ioc_sdiff_subset_right
    {N R q : ℕ} (hq : 1 ≤ q) :
    Finset.Ioc (N + q) (R - 1 + q) \ Finset.Ioc N R ⊆
      Finset.Ioc R (R - 1 + q) := by
  intro m hm
  rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hm
  rw [Finset.mem_Ioc]
  rcases hm with ⟨⟨hNqm, hmRq⟩, hmNot⟩
  refine ⟨?_, hmRq⟩
  by_contra hmLower
  apply hmNot
  constructor
  · omega
  · omega

/-- Two unit-modulus interval sums whose endpoints differ by the positive
translation `q` differ in norm by at most `2*q`. -/
theorem norm_sum_Ioc_sub_translated_le
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    {N R q : ℕ} (hq : 1 ≤ q) :
    ‖(∑ n ∈ Finset.Ioc N R, f n) -
        ∑ m ∈ Finset.Ioc (N + q) (R - 1 + q), f m‖ ≤
      2 * (q : ℝ) := by
  let A := Finset.Ioc N R
  let B := Finset.Ioc (N + q) (R - 1 + q)
  have hsplit :
      (∑ n ∈ A, f n) - ∑ n ∈ B, f n =
        (∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n := by
    rw [← A.sum_inter_add_sum_diff B f,
      ← B.sum_inter_add_sum_diff A f]
    rw [Finset.inter_comm B A]
    abel
  rw [hsplit]
  calc
    ‖(∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n‖ ≤
        ‖∑ n ∈ A \ B, f n‖ + ‖∑ n ∈ B \ A, f n‖ := norm_sub_le _ _
    _ ≤ (A \ B).card + (B \ A).card := by
      gcongr
      · calc
          ‖∑ n ∈ A \ B, f n‖ ≤ ∑ n ∈ A \ B, ‖f n‖ := norm_sum_le _ _
          _ = (A \ B).card := by simp [hf]
      · calc
          ‖∑ n ∈ B \ A, f n‖ ≤ ∑ n ∈ B \ A, ‖f n‖ := norm_sum_le _ _
          _ = (B \ A).card := by simp [hf]
    _ ≤ (Finset.Ioc N (N + q)).card +
          (Finset.Ioc R (R - 1 + q)).card := by
      norm_cast
      exact Nat.add_le_add
        (Finset.card_le_card (ford_Ioc_sdiff_shifted_subset_left hq))
        (Finset.card_le_card (ford_shifted_Ioc_sdiff_subset_right hq))
    _ ≤ 2 * (q : ℝ) := by
      rw [Nat.card_Ioc, Nat.card_Ioc]
      norm_cast
      omega

/-- The exact boundary count behind the preceding convenient `2*q` bound:
the left edge contributes at most `q` terms and the right edge at most
`q-1`.  This sharper form is needed when the source uses a real Weyl-shift
length and the actual finite sum is cut off at its floor. -/
theorem norm_sum_Ioc_sub_translated_le_sharp
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ = 1)
    {N R q : ℕ} (hR : 1 ≤ R) (hq : 1 ≤ q) :
    ‖(∑ n ∈ Finset.Ioc N R, f n) -
        ∑ m ∈ Finset.Ioc (N + q) (R - 1 + q), f m‖ ≤
      2 * (q : ℝ) - 1 := by
  let A := Finset.Ioc N R
  let B := Finset.Ioc (N + q) (R - 1 + q)
  have hsplit :
      (∑ n ∈ A, f n) - ∑ n ∈ B, f n =
        (∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n := by
    rw [← A.sum_inter_add_sum_diff B f,
      ← B.sum_inter_add_sum_diff A f]
    rw [Finset.inter_comm B A]
    abel
  rw [hsplit]
  calc
    ‖(∑ n ∈ A \ B, f n) - ∑ n ∈ B \ A, f n‖ ≤
        ‖∑ n ∈ A \ B, f n‖ + ‖∑ n ∈ B \ A, f n‖ := norm_sub_le _ _
    _ ≤ (A \ B).card + (B \ A).card := by
      gcongr
      · calc
          ‖∑ n ∈ A \ B, f n‖ ≤ ∑ n ∈ A \ B, ‖f n‖ := norm_sum_le _ _
          _ = (A \ B).card := by simp [hf]
      · calc
          ‖∑ n ∈ B \ A, f n‖ ≤ ∑ n ∈ B \ A, ‖f n‖ := norm_sum_le _ _
          _ = (B \ A).card := by simp [hf]
    _ ≤ (Finset.Ioc N (N + q)).card +
          (Finset.Ioc R (R - 1 + q)).card := by
      norm_cast
      exact Nat.add_le_add
        (Finset.card_le_card (ford_Ioc_sdiff_shifted_subset_left hq))
        (Finset.card_le_card (ford_shifted_Ioc_sdiff_subset_right hq))
    _ = 2 * (q : ℝ) - 1 := by
      have hleft : (Finset.Ioc N (N + q)).card = q := by
        rw [Nat.card_Ioc]
        omega
      have hright : (Finset.Ioc R (R - 1 + q)).card = q - 1 := by
        rw [Nat.card_Ioc]
        omega
      rw [hleft, hright]
      push_cast [Nat.cast_sub hq]
      ring

/-- The source sum and one common translated block differ by at most the
literal `2q` boundary allowance. -/
theorem norm_fordShiftedExponentialSum_sub_common_shift_le
    {N R q : ℕ} {u t : ℝ} (hq : 1 ≤ q) :
    ‖fordShiftedExponentialSum N R u t -
        ∑ n ∈ Finset.Ioc N (R - 1),
          fordShiftedLogPhase (n + q) u t‖ ≤
      2 * (q : ℝ) := by
  unfold fordShiftedExponentialSum
  rw [ford_sum_common_shift_eq_translated
    (fun n => fordShiftedLogPhase n u t) N R q]
  exact norm_sum_Ioc_sub_translated_le
    (fun n => fordShiftedLogPhase n u t)
    (fun n => norm_fordShiftedLogPhase n u t) hq

/-- Sharp `2*q-1` version of the source/common-block translation bound. -/
theorem norm_fordShiftedExponentialSum_sub_common_shift_le_sharp
    {N R q : ℕ} {u t : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q) :
    ‖fordShiftedExponentialSum N R u t -
        ∑ n ∈ Finset.Ioc N (R - 1),
          fordShiftedLogPhase (n + q) u t‖ ≤
      2 * (q : ℝ) - 1 := by
  unfold fordShiftedExponentialSum
  rw [ford_sum_common_shift_eq_translated
    (fun n => fordShiftedLogPhase n u t) N R q]
  exact norm_sum_Ioc_sub_translated_le_sharp
    (fun n => fordShiftedLogPhase n u t)
    (fun n => norm_fordShiftedLogPhase n u t) hR hq

end

end GafniTao
