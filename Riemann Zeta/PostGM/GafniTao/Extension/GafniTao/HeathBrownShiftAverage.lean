import GafniTao.HeathBrownKthDerivativeSetup
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Heath-Brown Lemma 1: exact translation average

The first step in Heath-Brown's proof averages `H` translates of the
exponential sum.  This file proves the exact finite identity and the complete
endpoint loss.  No differentiability or mean-value estimate is used here.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The translate by `h` of Heath-Brown's positive-index exponential sum. -/
noncomputable def heathBrownShiftedExponentialSum
    (N : ℕ) (f : ℝ → ℝ) (h : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, heathBrownPhase (f ((n + h : ℕ) : ℝ))

@[simp] theorem heathBrownShiftedExponentialSum_zero
    (N : ℕ) (f : ℝ → ℝ) :
    heathBrownShiftedExponentialSum N f 0 =
      heathBrownExponentialSum N f := by
  simp [heathBrownShiftedExponentialSum, heathBrownExponentialSum]

/-- Reindex a translate as the literal shifted interval. -/
theorem heathBrownShiftedExponentialSum_eq_interval
    (N : ℕ) (f : ℝ → ℝ) (h : ℕ) :
    heathBrownShiftedExponentialSum N f h =
      ∑ m ∈ Finset.Icc (1 + h) (N + h),
        heathBrownPhase (f (m : ℝ)) := by
  unfold heathBrownShiftedExponentialSum
  rw [← Finset.image_add_right_Icc 1 N h, Finset.sum_image]
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab

/-- Consecutive translates differ by precisely their two endpoint terms. -/
theorem heathBrownShiftedExponentialSum_succ_sub
    {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (h : ℕ) :
    heathBrownShiftedExponentialSum N f (h + 1) -
      heathBrownShiftedExponentialSum N f h =
      heathBrownPhase (f ((N + h + 1 : ℕ) : ℝ)) -
        heathBrownPhase (f ((h + 1 : ℕ) : ℝ)) := by
  rw [heathBrownShiftedExponentialSum_eq_interval,
    heathBrownShiftedExponentialSum_eq_interval]
  let a := h + 1
  let b := N + h
  have hab : a ≤ b := by
    dsimp only [a, b]
    omega
  have htop :
      (∑ m ∈ Finset.Icc a (b + 1), heathBrownPhase (f (m : ℝ))) =
        (∑ m ∈ Finset.Icc a b, heathBrownPhase (f (m : ℝ))) +
          heathBrownPhase (f ((b + 1 : ℕ) : ℝ)) := by
    exact Finset.sum_Icc_succ_top (by omega) _
  have hbottom :
      (∑ m ∈ Finset.Icc a (b + 1), heathBrownPhase (f (m : ℝ))) =
        heathBrownPhase (f (a : ℝ)) +
          ∑ m ∈ Finset.Icc (a + 1) (b + 1),
            heathBrownPhase (f (m : ℝ)) := by
    rw [← Finset.insert_Icc_add_one_left_eq_Icc
      (by omega : a ≤ b + 1)]
    exact Finset.sum_insert (by simp)
  dsimp only [a, b] at htop hbottom ⊢
  have hNform : N + (h + 1) = N + h + 1 := by omega
  have honeform : 1 + (h + 1) = h + 1 + 1 := by omega
  rw [hNform, honeform]
  simp only [Nat.one_add] at htop hbottom ⊢
  push_cast at htop hbottom ⊢
  linear_combination htop - hbottom

/-- The norm lost by a single unit translate is at most two. -/
theorem norm_heathBrownShiftedExponentialSum_succ_sub_le_two
    {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (h : ℕ) :
    ‖heathBrownShiftedExponentialSum N f (h + 1) -
        heathBrownShiftedExponentialSum N f h‖ ≤ 2 := by
  rw [heathBrownShiftedExponentialSum_succ_sub hN]
  calc
    ‖heathBrownPhase (f ((N + h + 1 : ℕ) : ℝ)) -
        heathBrownPhase (f ((h + 1 : ℕ) : ℝ))‖ ≤
      ‖heathBrownPhase (f ((N + h + 1 : ℕ) : ℝ))‖ +
        ‖heathBrownPhase (f ((h + 1 : ℕ) : ℝ))‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_heathBrownPhase, norm_heathBrownPhase]; norm_num

/-- Translating by `h` loses at most the `2h` endpoint terms. -/
theorem norm_heathBrownShiftedExponentialSum_sub_le
    {N : ℕ} (hN : 1 ≤ N) (f : ℝ → ℝ) (h : ℕ) :
    ‖heathBrownShiftedExponentialSum N f h -
        heathBrownExponentialSum N f‖ ≤ 2 * h := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hstep :=
        norm_heathBrownShiftedExponentialSum_succ_sub_le_two hN f h
      calc
        ‖heathBrownShiftedExponentialSum N f (h + 1) -
            heathBrownExponentialSum N f‖ =
          ‖(heathBrownShiftedExponentialSum N f (h + 1) -
              heathBrownShiftedExponentialSum N f h) +
            (heathBrownShiftedExponentialSum N f h -
              heathBrownExponentialSum N f)‖ := by ring_nf
        _ ≤ ‖heathBrownShiftedExponentialSum N f (h + 1) -
              heathBrownShiftedExponentialSum N f h‖ +
            ‖heathBrownShiftedExponentialSum N f h -
              heathBrownExponentialSum N f‖ := norm_add_le _ _
        _ ≤ 2 + 2 * (h : ℝ) := add_le_add hstep ih
        _ = 2 * ((h + 1 : ℕ) : ℝ) := by push_cast; ring

/-- Exact algebraic form of the translation-average remainder. -/
theorem heathBrown_translation_average_sub_eq
    (N H : ℕ) (f : ℝ → ℝ) :
    (∑ h ∈ Finset.Icc 1 H, heathBrownShiftedExponentialSum N f h) -
        (H : ℂ) * heathBrownExponentialSum N f =
      ∑ h ∈ Finset.Icc 1 H,
        (heathBrownShiftedExponentialSum N f h -
          heathBrownExponentialSum N f) := by
  rw [Finset.sum_sub_distrib]
  have hcard : (Finset.Icc 1 H).card = H := by
    simp [Nat.card_Icc]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- The complete source endpoint ledger: averaging `H` translates changes
`H S` by at most `H(H+1)`. -/
theorem norm_heathBrown_translation_average_sub_le
    {N : ℕ} (hN : 1 ≤ N) (H : ℕ) (f : ℝ → ℝ) :
    ‖(∑ h ∈ Finset.Icc 1 H, heathBrownShiftedExponentialSum N f h) -
        (H : ℂ) * heathBrownExponentialSum N f‖ ≤
      (H : ℝ) * (H + 1) := by
  rw [heathBrown_translation_average_sub_eq]
  calc
    ‖∑ h ∈ Finset.Icc 1 H,
        (heathBrownShiftedExponentialSum N f h -
          heathBrownExponentialSum N f)‖ ≤
      ∑ h ∈ Finset.Icc 1 H,
        ‖heathBrownShiftedExponentialSum N f h -
          heathBrownExponentialSum N f‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 H, (2 * h : ℝ) := by
      gcongr with h hh
      exact norm_heathBrownShiftedExponentialSum_sub_le hN f h
    _ = (H : ℝ) * (H + 1) := by
      induction H with
      | zero => simp
      | succ H ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ H + 1)]
          rw [ih]
          push_cast
          ring

#print axioms heathBrownShiftedExponentialSum_zero
#print axioms heathBrownShiftedExponentialSum_eq_interval
#print axioms heathBrownShiftedExponentialSum_succ_sub
#print axioms norm_heathBrownShiftedExponentialSum_succ_sub_le_two
#print axioms norm_heathBrownShiftedExponentialSum_sub_le
#print axioms heathBrown_translation_average_sub_eq
#print axioms norm_heathBrown_translation_average_sub_le

end

end GafniTao
