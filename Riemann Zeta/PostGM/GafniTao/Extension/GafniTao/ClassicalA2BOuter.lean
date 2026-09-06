import GafniTao.ClassicalA2BInner

/-!
# The complete finite `A²B` logarithmic estimate

The inner A-process is converted from its squared form to an explicit norm
majorant.  That majorant is then used, distance by distance, in the outer
A-process.  Both integer shift lengths and all endpoint losses remain visible.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicDifferenceA2Majorant
    (t A : ℝ) (r N H : ℕ) : ℝ :=
  ((N + H : ℕ) : ℝ) *
    ((H : ℝ) * N + (H : ℝ) *
      (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
        logarithmicSecondCorrelationBound t A N r s))

noncomputable def logarithmicDifferenceA2Bound
    (t A : ℝ) (r N H : ℕ) : ℝ :=
  Real.sqrt (logarithmicDifferenceA2Majorant t A r N H) / H

theorem norm_logarithmicDifferenceSum_le_A2Bound
    (t A : ℝ) (r N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hHpos : 0 < H) (hH : H ≤ N) (hNAr : (N : ℝ) + r ≤ A) :
    ‖∑ n ∈ Finset.range N,
      unitaryPhase (logarithmicDifferencePhase t A 0 r n)‖ ≤
      logarithmicDifferenceA2Bound t A r N H := by
  have hsquared := logarithmicDifference_weyl_AB_process
    t A r N H ht hA hr hH hNAr
  rw [integerPhaseSum_eq_range] at hsquared
  have hsq :
      (((H : ℝ) * ‖∑ n ∈ Finset.range N,
        unitaryPhase (logarithmicDifferencePhase t A 0 r n)‖) ^ 2) ≤
        logarithmicDifferenceA2Majorant t A r N H := by
    unfold logarithmicDifferenceA2Majorant
    nlinarith
  have hsqrt :
      (H : ℝ) * ‖∑ n ∈ Finset.range N,
        unitaryPhase (logarithmicDifferencePhase t A 0 r n)‖ ≤
        Real.sqrt (logarithmicDifferenceA2Majorant t A r N H) :=
    Real.le_sqrt_of_sq_le hsq
  unfold logarithmicDifferenceA2Bound
  rw [le_div_iff₀ (Nat.cast_pos.mpr hHpos)]
  simpa only [mul_comm] using hsqrt

theorem padded_logarithmic_correlation_norm_le_A2_of_lt
    (t A : ℝ) (N H₁ H₂ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hh : h < H₁) (hk : k < H₁) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
      logarithmicDifferenceA2Bound t A (k - h) (N - (k - h)) H₂ := by
  have hr : 0 < k - h := Nat.sub_pos_of_lt hhk
  have hrHigh : k - h ≤ H₁ - 1 := by omega
  have hrN : k - h ≤ N :=
    hrHigh.trans ((Nat.sub_le H₁ 1).trans hH₁)
  have hH₂' : H₂ ≤ N - (k - h) := by omega
  have hsize : ((N - (k - h) : ℕ) : ℝ) + ((k - h : ℕ) : ℝ) ≤ A := by
    calc
      ((N - (k - h) : ℕ) : ℝ) + ((k - h : ℕ) : ℝ)
          = (((N - (k - h)) + (k - h) : ℕ) : ℝ) := by norm_num
      _ = (N : ℝ) := by rw [Nat.sub_add_cancel hrN]
      _ ≤ A := hNA
  rw [padded_logarithmic_correlation_eq t A N H₁ h k hh hk hhk,
    norm_star]
  exact norm_logarithmicDifferenceSum_le_A2Bound
    t A (k - h) (N - (k - h)) H₂ ht hA hr hH₂pos hH₂' hsize

noncomputable def logarithmicA2BCorrelationBound
    (t A : ℝ) (N H₂ r : ℕ) : ℝ :=
  logarithmicDifferenceA2Bound t A r (N - r) H₂

theorem logarithmicA2BCorrelationBound_nonneg
    (t A : ℝ) (N H₂ r : ℕ) (hH₂ : 0 < H₂) :
    0 ≤ logarithmicA2BCorrelationBound t A N H₂ r := by
  unfold logarithmicA2BCorrelationBound logarithmicDifferenceA2Bound
  positivity

theorem padded_logarithmic_correlation_norm_le_A2
    (t A : ℝ) (N H₁ H₂ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₂ : H₂ ≤ N - (H₁ - 1))
    (hh : h < H₁) (hk : k < H₁) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
      logarithmicA2BCorrelationBound t A N H₂
        (finiteShiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmic_correlation_norm_le_A2_of_lt
      t A N H₁ H₂ h k ht hA hNA hH₁ hH₂pos hH₂ hh hk hhk
    simpa only [logarithmicA2BCorrelationBound, finiteShiftDistance,
      Nat.sub_eq_zero_of_le hhk.le, zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmic_correlation_norm_le_A2_of_lt
      t A N H₁ H₂ k h ht hA hNA hH₁ hH₂pos hH₂ hk hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k
    let w := ∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n k) *
        paddedShift (integerLogarithmicTerm t A) N n h
    have hzw : z = star w := by
      dsimp only [z, w]
      change (∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
        star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k) =
        (starRingEnd ℂ) (∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
          star (paddedShift (integerLogarithmicTerm t A) N n k) *
            paddedShift (integerLogarithmicTerm t A) N n h)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      change star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k =
        star (star (paddedShift (integerLogarithmicTerm t A) N n k) *
          paddedShift (integerLogarithmicTerm t A) N n h)
      rw [star_mul', star_star]
      ring
    rw [show ‖z‖ = ‖w‖ by rw [hzw, norm_star]]
    simpa only [logarithmicA2BCorrelationBound, finiteShiftDistance,
      Nat.sub_eq_zero_of_le hkh.le, add_zero] using hb

/-- Complete finite `A²B` bound for a logarithmic block. -/
theorem logarithmic_weyl_A2B_process
    (t A : ℝ) (N H₁ H₂ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₂ : H₂ ≤ N - (H₁ - 1)) :
    (H₁ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerLogarithmicTerm t A n‖ ^ 2 ≤
      ((N + H₁ : ℕ) : ℝ) *
        ((H₁ : ℝ) * N + (H₁ : ℝ) *
          (2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
            logarithmicA2BCorrelationBound t A N H₂ r)) := by
  apply interval_weyl_differencing_row_complex
    (integerLogarithmicTerm t A) N H₁
    (2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
      logarithmicA2BCorrelationBound t A N H₂ r)
  · intro n _hn
    simp
  · intro h hh
    calc
      ∑ k ∈ (Finset.range H₁).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
            star (paddedShift (integerLogarithmicTerm t A) N n h) *
              paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
        ∑ k ∈ (Finset.range H₁).filter (fun k => k ≠ h),
          logarithmicA2BCorrelationBound t A N H₂
            (finiteShiftDistance h k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact padded_logarithmic_correlation_norm_le_A2
            t A N H₁ H₂ h k ht hA hNA hH₁ hH₂pos hH₂
              (Finset.mem_range.mp hh)
              (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
              (Ne.symm (Finset.mem_filter.mp hk).2)
      _ ≤ 2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicA2BCorrelationBound t A N H₂ r :=
        sum_shiftDistance_le_two_mul_sum
          (fun r => logarithmicA2BCorrelationBound t A N H₂ r)
          (fun r => logarithmicA2BCorrelationBound_nonneg t A N H₂ r hH₂pos)
          (Finset.mem_range.mp hh)

#print axioms norm_logarithmicDifferenceSum_le_A2Bound
#print axioms padded_logarithmic_correlation_norm_le_A2_of_lt
#print axioms logarithmic_weyl_A2B_process

end

end GafniTao
