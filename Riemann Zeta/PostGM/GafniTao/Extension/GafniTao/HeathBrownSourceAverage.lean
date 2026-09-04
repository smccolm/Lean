import GafniTao.HeathBrownShiftAverage

/-!
# Heath-Brown Lemma 1: the source truncation

Heath-Brown first rewrites every copy of the original sum using
`-h < n ≤ N-h`, and then restricts the common inner range to
`1 ≤ n ≤ N-H`.  After the change of variables `m=n+h`, the omitted
indices have total cardinality exactly `H` for each `h`.  The theorem below
therefore proves the paper's `O(H^2)` remainder with constant one.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The common inner range in equation `(Σ1)` of Heath-Brown's paper. -/
noncomputable def heathBrownSourceShiftSum
    (N H : ℕ) (f : ℝ → ℝ) (h : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N - H),
    heathBrownPhase (f ((n + h : ℕ) : ℝ))

theorem heathBrownSourceShiftSum_eq_interval
    (N H : ℕ) (f : ℝ → ℝ) (h : ℕ) :
    heathBrownSourceShiftSum N H f h =
      ∑ m ∈ Finset.Icc (1 + h) (N - H + h),
        heathBrownPhase (f (m : ℝ)) := by
  unfold heathBrownSourceShiftSum
  rw [← Finset.image_add_right_Icc 1 (N - H) h, Finset.sum_image]
  intro a ha b hb hab
  exact Nat.add_right_cancel hab

theorem heathBrown_source_shift_interval_subset
    {N H h : ℕ} (hHN : H ≤ N) (hh : h ≤ H) :
    Finset.Icc (1 + h) (N - H + h) ⊆ Finset.Icc 1 N := by
  intro m hm
  simp only [Finset.mem_Icc] at hm ⊢
  constructor
  · omega
  · omega

theorem heathBrown_source_shift_omitted_card
    {N H h : ℕ} (hHN : H ≤ N) (hh : h ≤ H) :
    (Finset.Icc 1 N \ Finset.Icc (1 + h) (N - H + h)).card = H := by
  let S := Finset.Icc 1 N
  let T := Finset.Icc (1 + h) (N - H + h)
  have hTS : T ⊆ S := by
    exact heathBrown_source_shift_interval_subset hHN hh
  have hinter : T ∩ S = T := Finset.inter_eq_left.mpr hTS
  have hcardS : S.card = N := by
    dsimp only [S]
    simp [Nat.card_Icc]
  have hcardT : T.card = N - H := by
    dsimp only [T]
    simp [Nat.card_Icc]
    omega
  rw [Finset.card_sdiff, hinter, hcardS, hcardT]
  omega

/-- A fixed source shift omits at most `H` unit-modulus summands. -/
theorem norm_heathBrownExponentialSum_sub_sourceShift_le
    {N H h : ℕ} (hHN : H ≤ N) (hh : h ≤ H) (f : ℝ → ℝ) :
    ‖heathBrownExponentialSum N f -
        heathBrownSourceShiftSum N H f h‖ ≤ H := by
  rw [heathBrownSourceShiftSum_eq_interval]
  let S := Finset.Icc 1 N
  let T := Finset.Icc (1 + h) (N - H + h)
  let a : ℕ → ℂ := fun m => heathBrownPhase (f (m : ℝ))
  have hTS : T ⊆ S := heathBrown_source_shift_interval_subset hHN hh
  have hsplit := Finset.sum_sdiff hTS (f := a)
  have hdiff :
      (∑ m ∈ S, a m) - (∑ m ∈ T, a m) = ∑ m ∈ S \ T, a m := by
    rw [← hsplit]
    ring
  change ‖(∑ m ∈ S, a m) - (∑ m ∈ T, a m)‖ ≤ H
  rw [hdiff]
  calc
    ‖∑ m ∈ S \ T, a m‖ ≤ ∑ m ∈ S \ T, ‖a m‖ := norm_sum_le _ _
    _ = (S \ T).card := by
      simp only [a, norm_heathBrownPhase, sum_const, nsmul_eq_mul]
      simp
    _ = H := by
      exact_mod_cast heathBrown_source_shift_omitted_card hHN hh

/-- Exact finite identity behind the `O(H^2)` term. -/
theorem heathBrown_source_average_sub_eq
    (N H : ℕ) (f : ℝ → ℝ) :
    (H : ℂ) * heathBrownExponentialSum N f -
        ∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h =
      ∑ h ∈ Finset.Icc 1 H,
        (heathBrownExponentialSum N f -
          heathBrownSourceShiftSum N H f h) := by
  rw [Finset.sum_sub_distrib]
  have hcard : (Finset.Icc 1 H).card = H := by
    simp [Nat.card_Icc]
  rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Heath-Brown equation `(Σ1)` before division by `H`, with the complete
endpoint error and no unspecified big-O constant. -/
theorem norm_heathBrown_source_average_sub_le
    {N H : ℕ} (hHN : H ≤ N) (f : ℝ → ℝ) :
    ‖(H : ℂ) * heathBrownExponentialSum N f -
        ∑ h ∈ Finset.Icc 1 H, heathBrownSourceShiftSum N H f h‖ ≤
      (H : ℝ) ^ 2 := by
  rw [heathBrown_source_average_sub_eq]
  calc
    ‖∑ h ∈ Finset.Icc 1 H,
        (heathBrownExponentialSum N f -
          heathBrownSourceShiftSum N H f h)‖ ≤
      ∑ h ∈ Finset.Icc 1 H,
        ‖heathBrownExponentialSum N f -
          heathBrownSourceShiftSum N H f h‖ := norm_sum_le _ _
    _ ≤ ∑ _h ∈ Finset.Icc 1 H, (H : ℝ) := by
      gcongr with h hh
      exact norm_heathBrownExponentialSum_sub_sourceShift_le hHN
        (Finset.mem_Icc.mp hh).2 f
    _ = (H : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Nat.card_Icc, pow_two]

#print axioms heathBrownSourceShiftSum_eq_interval
#print axioms heathBrown_source_shift_interval_subset
#print axioms heathBrown_source_shift_omitted_card
#print axioms norm_heathBrownExponentialSum_sub_sourceShift_le
#print axioms heathBrown_source_average_sub_eq
#print axioms norm_heathBrown_source_average_sub_le

end

end GafniTao
