import GafniTao.ClassicalA3BMajorants

/-!
# The middle `A` process in the finite `A³B` estimate

The exact third-difference bound is used as the correlation input for the
second `A` process.  All integer endpoint losses remain explicit.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicA3SecondCorrelationBound
    (t A : ℝ) (N r H₃ s : ℕ) : ℝ :=
  logarithmicSecondDifferenceA3Bound t A r s (N - s) H₃

theorem logarithmicA3SecondCorrelationBound_nonneg
    (t A : ℝ) (N r H₃ s : ℕ) (hH₃ : 0 < H₃) :
    0 ≤ logarithmicA3SecondCorrelationBound t A N r H₃ s := by
  unfold logarithmicA3SecondCorrelationBound
    logarithmicSecondDifferenceA3Bound
  positivity

theorem padded_logarithmicDifference_correlation_norm_le_A3_of_lt
    (t A : ℝ) (r N H₂ H₃ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hk : k < H₂) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
      logarithmicA3SecondCorrelationBound t A N r H₃ (k - h) := by
  have hs : 0 < k - h := Nat.sub_pos_of_lt hhk
  have hsHigh : k - h ≤ H₂ - 1 := by omega
  have hsN : k - h ≤ N := hsHigh.trans ((Nat.sub_le H₂ 1).trans hH₂)
  have hH₃' : H₃ ≤ N - (k - h) := by omega
  have hsize : (((N - (k - h) : ℕ) : ℝ)) + (r : ℝ) +
      (((k - h : ℕ) : ℝ)) ≤ A := by
    calc
      (((N - (k - h) : ℕ) : ℝ)) + (r : ℝ) + (((k - h : ℕ) : ℝ)) =
          (N : ℝ) + r := by
        rw [Nat.cast_sub hsN]
        ring
      _ ≤ A := hNAr
  rw [padded_logarithmicDifference_correlation_eq t A r N H₂ h k hk hhk,
    norm_star]
  exact norm_logarithmicSecondDifferenceSum_le_A3Bound
    t A r (k - h) (N - (k - h)) H₃ ht hA hr hs hH₃pos hH₃' hsize

theorem padded_logarithmicDifference_correlation_norm_le_A3
    (t A : ℝ) (r N H₂ H₃ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hh : h < H₂) (hk : k < H₂) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
      logarithmicA3SecondCorrelationBound t A N r H₃
        (finiteShiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmicDifference_correlation_norm_le_A3_of_lt
      t A r N H₂ H₃ h k ht hA hr hNAr hH₂ hH₃pos hH₃ hk hhk
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hhk.le,
      zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmicDifference_correlation_norm_le_A3_of_lt
      t A r N H₂ H₃ k h ht hA hr hNAr hH₂ hH₃pos hH₃ hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k
    let w := ∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h
    have hzw : z = star w := by
      dsimp only [z, w]
      change (∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
        star (paddedShift
          (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
        paddedShift
          (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) =
        (starRingEnd ℂ) (∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
          star (paddedShift
            (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) *
          paddedShift
            (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      change star (paddedShift
          (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
          paddedShift
            (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k =
        star (star (paddedShift
            (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) *
          paddedShift
            (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h)
      rw [star_mul', star_star]
      ring
    rw [show ‖z‖ = ‖w‖ by rw [hzw, norm_star]]
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hkh.le,
      add_zero] using hb

theorem logarithmicDifference_weyl_A2B_process_A3
    (t A : ℝ) (r N H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1)) :
    (H₂ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ^ 2 ≤
      ((N + H₂ : ℕ) : ℝ) *
        ((H₂ : ℝ) * N + (H₂ : ℝ) *
          (2 * ∑ s ∈ Finset.Icc 1 (H₂ - 1),
            logarithmicA3SecondCorrelationBound t A N r H₃ s)) := by
  apply interval_weyl_differencing_row_complex
    (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N H₂
    (2 * ∑ s ∈ Finset.Icc 1 (H₂ - 1),
      logarithmicA3SecondCorrelationBound t A N r H₃ s)
  · intro n _hn
    simp
  · intro h hh
    calc
      ∑ k ∈ (Finset.range H₂).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H₂ : ℤ)) N,
            star (paddedShift
              (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
            paddedShift
              (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
        ∑ k ∈ (Finset.range H₂).filter (fun k => k ≠ h),
          logarithmicA3SecondCorrelationBound t A N r H₃
            (finiteShiftDistance h k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact padded_logarithmicDifference_correlation_norm_le_A3
            t A r N H₂ H₃ h k ht hA hr hNAr hH₂ hH₃pos hH₃
              (Finset.mem_range.mp hh)
              (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
              (Ne.symm (Finset.mem_filter.mp hk).2)
      _ ≤ 2 * ∑ s ∈ Finset.Icc 1 (H₂ - 1),
          logarithmicA3SecondCorrelationBound t A N r H₃ s :=
        sum_shiftDistance_le_two_mul_sum
          (fun s => logarithmicA3SecondCorrelationBound t A N r H₃ s)
          (fun s => logarithmicA3SecondCorrelationBound_nonneg
            t A N r H₃ s hH₃pos) (Finset.mem_range.mp hh)

#print axioms padded_logarithmicDifference_correlation_norm_le_A3_of_lt
#print axioms logarithmicDifference_weyl_A2B_process_A3

end

end GafniTao
