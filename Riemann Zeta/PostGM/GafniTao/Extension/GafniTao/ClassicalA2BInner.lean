import GafniTao.ClassicalPaddedPhaseCorrelation
import GafniTao.ClassicalExponentPairAveraging

/-!
# The inner B process in the classical `A²B` construction

This module identifies the second correlation phase produced by applying
Weyl differencing to a first logarithmic difference, and applies the finite
van der Corput B process with both shift distances explicit.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem phaseForwardDifference_logarithmicDifferencePhase
    (t A : ℝ) (r s : ℕ) (x : ℝ) :
    phaseForwardDifference (logarithmicDifferencePhase t A 0 r) s x =
      logarithmicSecondDifferencePhase t A r s x := by
  rfl

/-- The B-process estimate for the two-shift logarithmic phase. -/
theorem logarithmicSecondDifference_B_process
    (t A : ℝ) (r s N : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hs : 0 < s)
    (hsize : ((N + 1 + r + s : ℕ) : ℝ) ≤ A) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (logarithmicSecondDifferencePhase t A r s n)‖ ≤
      ((N : ℝ) * (32 * t * r * s / A ^ 4) /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (t * r * s / (16 * A ^ 4)) +
          2 * (Real.sqrt (t * r * s / (16 * A ^ 4)) /
            (t * r * s / (16 * A ^ 4)) + 1)) := by
  let lambda : ℝ := t * r * s / (16 * A ^ 4)
  let Lambda : ℝ := 32 * t * r * s / A ^ 4
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  have hbounds := logarithmicSecondDifference_secondDifference_bounds
    t A r s N ht hA hr hs hsize
  simpa only [lambda, Lambda] using
    vanDerCorput_B_process
      (fun n : ℕ => logarithmicSecondDifferencePhase t A r s n)
      N lambda Lambda hlambda
      (fun n hn => by
        simpa only [lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          (hbounds n hn).1)
      (fun n hn => by
        simpa only [Lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          (hbounds n hn).2)

/-- Exact inner correlation identity after the second A-process shift. -/
theorem padded_logarithmicDifference_correlation_eq
    (t A : ℝ) (r N H h k : ℕ)
    (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) =
      star (∑ m ∈ Finset.range (N - (k - h)),
        unitaryPhase
          (logarithmicSecondDifferencePhase t A r (k - h) m)) := by
  simpa only [phaseForwardDifference_logarithmicDifferencePhase] using
    padded_phase_correlation_eq
      (logarithmicDifferencePhase t A 0 r) N H h k hk hhk

/-! The majorant keeps the finite length and both shift distances literal. -/
noncomputable def logarithmicSecondCorrelationBound
    (t A : ℝ) (N r s : ℕ) : ℝ :=
  let M := N - s - 1
  ((M : ℝ) * (32 * t * r * s / A ^ 4) /
      (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r * s / (16 * A ^ 4)) +
      2 * (Real.sqrt (t * r * s / (16 * A ^ 4)) /
        (t * r * s / (16 * A ^ 4)) + 1))

theorem logarithmicSecondCorrelationBound_nonneg
    (t A : ℝ) (N r s : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) :
    0 ≤ logarithmicSecondCorrelationBound t A N r s := by
  unfold logarithmicSecondCorrelationBound
  positivity

theorem padded_logarithmicDifference_correlation_norm_le_of_lt
    (t A : ℝ) (r N H h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : H ≤ N)
    (hNAr : (N : ℝ) + r ≤ A) (hr : 0 < r)
    (hk : k < H) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
      logarithmicSecondCorrelationBound t A N r (k - h) := by
  have hs : 0 < k - h := Nat.sub_pos_of_lt hhk
  let M := N - (k - h) - 1
  have hlength : M + 1 = N - (k - h) := by
    dsimp only [M]
    omega
  rw [padded_logarithmicDifference_correlation_eq t A r N H h k hk hhk,
    norm_star, ← hlength]
  have hsizeNat : M + 1 + r + (k - h) ≤ N + r := by
    dsimp only [M]
    omega
  have hsize' : ((M + 1 + r + (k - h) : ℕ) : ℝ) ≤ A := by
    calc
      ((M + 1 + r + (k - h) : ℕ) : ℝ)
          ≤ ((N + r : ℕ) : ℝ) := Nat.cast_le.mpr hsizeNat
      _ = (N : ℝ) + r := by norm_num
      _ ≤ A := hNAr
  have hB' := logarithmicSecondDifference_B_process
    t A r (k - h) M ht hA hr hs hsize'
  simpa only [logarithmicSecondCorrelationBound, M] using hB'

theorem padded_logarithmicDifference_correlation_norm_le
    (t A : ℝ) (r N H h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : H ≤ N)
    (hNAr : (N : ℝ) + r ≤ A) (hr : 0 < r)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
      logarithmicSecondCorrelationBound t A N r
        (finiteShiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmicDifference_correlation_norm_le_of_lt
      t A r N H h k ht hA hH hNAr hr hk hhk
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hhk.le,
      zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmicDifference_correlation_norm_le_of_lt
      t A r N H k h ht hA hH hNAr hr hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k
    let w := ∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) *
      paddedShift
        (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h
    have hzw : z = star w := by
      dsimp only [z, w]
      change (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
        star (paddedShift
          (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
        paddedShift
          (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k) =
        (starRingEnd ℂ) (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
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

/-- The second A process with its row sum retained, followed by the exact
two-shift B-process. -/
theorem logarithmicDifference_weyl_AB_process
    (t A : ℝ) (r N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (hH : H ≤ N) (hNAr : (N : ℝ) + r ≤ A) :
    (H : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
            logarithmicSecondCorrelationBound t A N r s)) := by
  apply interval_weyl_differencing_row_complex
    (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N H
    (2 * ∑ s ∈ Finset.Icc 1 (H - 1),
      logarithmicSecondCorrelationBound t A N r s)
  · intro n _hn
    simp
  · intro h hh
    calc
      ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
            star (paddedShift
              (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n h) *
            paddedShift
              (integerPhaseTerm (logarithmicDifferencePhase t A 0 r)) N n k‖ ≤
        ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          logarithmicSecondCorrelationBound t A N r
            (finiteShiftDistance h k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact padded_logarithmicDifference_correlation_norm_le
            t A r N H h k ht hA hH hNAr hr
              (Finset.mem_range.mp hh)
              (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
              (Ne.symm (Finset.mem_filter.mp hk).2)
      _ ≤ 2 * ∑ s ∈ Finset.Icc 1 (H - 1),
          logarithmicSecondCorrelationBound t A N r s :=
        sum_shiftDistance_le_two_mul_sum
          (fun s => logarithmicSecondCorrelationBound t A N r s)
          (fun s => logarithmicSecondCorrelationBound_nonneg
            t A N r s ht hA hr) (Finset.mem_range.mp hh)

#print axioms logarithmicSecondDifference_B_process
#print axioms padded_logarithmicDifference_correlation_eq
#print axioms logarithmicDifference_weyl_AB_process

end

end GafniTao
