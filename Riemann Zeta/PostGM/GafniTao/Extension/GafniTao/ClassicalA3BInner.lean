import GafniTao.ClassicalA3BLogCurvature
import GafniTao.ClassicalPaddedPhaseCorrelation

/-!
# The innermost `AB` process in the classical `A³B` construction

This module applies the finite `B` process to the third logarithmic
difference, then packages it as the row-averaged `A` process for a fixed
two-shift logarithmic phase.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem phaseForwardDifference_logarithmicSecondDifferencePhase
    (t A : ℝ) (r s q : ℕ) (x : ℝ) :
    phaseForwardDifference (logarithmicSecondDifferencePhase t A r s) q x =
      logarithmicThirdDifferencePhase t A r s q x := by
  rfl

theorem logarithmicThirdDifference_B_process
    (t A : ℝ) (r s q N : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hsize : ((N + 1 + r + s + q : ℕ) : ℝ) ≤ A) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (logarithmicThirdDifferencePhase t A r s q n)‖ ≤
      ((N : ℝ) * (192 * t * r * s * q / A ^ 5) /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (t * r * s * q / (16 * A ^ 5)) +
          2 * (Real.sqrt (t * r * s * q / (16 * A ^ 5)) /
            (t * r * s * q / (16 * A ^ 5)) + 1)) := by
  let lambda : ℝ := t * r * s * q / (16 * A ^ 5)
  let Lambda : ℝ := 192 * t * r * s * q / A ^ 5
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  have hbounds := logarithmicThirdDifference_secondDifference_bounds
    t A r s q N ht hA hr hs hq hsize
  simpa only [lambda, Lambda] using
    vanDerCorput_B_process
      (fun n : ℕ => logarithmicThirdDifferencePhase t A r s q n)
      N lambda Lambda hlambda
      (fun n hn => by
        simpa only [lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          (hbounds n hn).1)
      (fun n hn => by
        simpa only [Lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
          (hbounds n hn).2)

theorem padded_logarithmicSecondDifference_correlation_eq
    (t A : ℝ) (r s N H h k : ℕ)
    (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k) =
      star (∑ m ∈ Finset.range (N - (k - h)),
        unitaryPhase
          (logarithmicThirdDifferencePhase t A r s (k - h) m)) := by
  simpa only [phaseForwardDifference_logarithmicSecondDifferencePhase] using
    padded_phase_correlation_eq
      (logarithmicSecondDifferencePhase t A r s) N H h k hk hhk

noncomputable def logarithmicThirdCorrelationBound
    (t A : ℝ) (N r s q : ℕ) : ℝ :=
  let M := N - q - 1
  ((M : ℝ) * (192 * t * r * s * q / A ^ 5) /
      (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r * s * q / (16 * A ^ 5)) +
      2 * (Real.sqrt (t * r * s * q / (16 * A ^ 5)) /
        (t * r * s * q / (16 * A ^ 5)) + 1))

theorem logarithmicThirdCorrelationBound_nonneg
    (t A : ℝ) (N r s q : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hs : 0 < s) :
    0 ≤ logarithmicThirdCorrelationBound t A N r s q := by
  unfold logarithmicThirdCorrelationBound
  positivity

theorem padded_logarithmicSecondDifference_correlation_norm_le_of_lt
    (t A : ℝ) (r s N H h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : H ≤ N)
    (hNArs : (N : ℝ) + r + s ≤ A) (hr : 0 < r) (hs : 0 < s)
    (hk : k < H) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k‖ ≤
      logarithmicThirdCorrelationBound t A N r s (k - h) := by
  have hq : 0 < k - h := Nat.sub_pos_of_lt hhk
  let M := N - (k - h) - 1
  have hlength : M + 1 = N - (k - h) := by
    dsimp only [M]
    omega
  rw [padded_logarithmicSecondDifference_correlation_eq
    t A r s N H h k hk hhk, norm_star, ← hlength]
  have hsizeNat : M + 1 + r + s + (k - h) ≤ N + r + s := by
    dsimp only [M]
    omega
  have hsize' : ((M + 1 + r + s + (k - h) : ℕ) : ℝ) ≤ A := by
    calc
      ((M + 1 + r + s + (k - h) : ℕ) : ℝ) ≤
          ((N + r + s : ℕ) : ℝ) := Nat.cast_le.mpr hsizeNat
      _ = (N : ℝ) + r + s := by norm_num
      _ ≤ A := hNArs
  have hB' := logarithmicThirdDifference_B_process
    t A r s (k - h) M ht hA hr hs hq hsize'
  simpa only [logarithmicThirdCorrelationBound, M] using hB'

theorem padded_logarithmicSecondDifference_correlation_norm_le
    (t A : ℝ) (r s N H h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : H ≤ N)
    (hNArs : (N : ℝ) + r + s ≤ A) (hr : 0 < r) (hs : 0 < s)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k‖ ≤
      logarithmicThirdCorrelationBound t A N r s
        (finiteShiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmicSecondDifference_correlation_norm_le_of_lt
      t A r s N H h k ht hA hH hNArs hr hs hk hhk
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hhk.le,
      zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmicSecondDifference_correlation_norm_le_of_lt
      t A r s N H k h ht hA hH hNArs hr hs hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
      paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k
    let w := ∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k) *
      paddedShift
        (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h
    have hzw : z = star w := by
      dsimp only [z, w]
      change (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
        star (paddedShift
          (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
        paddedShift
          (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k) =
        (starRingEnd ℂ) (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
          star (paddedShift
            (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k) *
          paddedShift
            (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      change star (paddedShift
          (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
          paddedShift
            (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k =
        star (star (paddedShift
            (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k) *
          paddedShift
            (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h)
      rw [star_mul', star_star]
      ring
    rw [show ‖z‖ = ‖w‖ by rw [hzw, norm_star]]
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hkh.le,
      add_zero] using hb

theorem logarithmicSecondDifference_weyl_AB_process
    (t A : ℝ) (r s N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ N) (hNArs : (N : ℝ) + r + s ≤ A) :
    (H : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerPhaseTerm (logarithmicSecondDifferencePhase t A r s) n‖ ^ 2 ≤
      ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
            logarithmicThirdCorrelationBound t A N r s q)) := by
  apply interval_weyl_differencing_row_complex
    (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N H
    (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
      logarithmicThirdCorrelationBound t A N r s q)
  · intro n _hn
    simp
  · intro h hh
    calc
      ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H : ℤ)) N,
            star (paddedShift
              (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n h) *
            paddedShift
              (integerPhaseTerm (logarithmicSecondDifferencePhase t A r s)) N n k‖ ≤
        ∑ k ∈ (Finset.range H).filter (fun k => k ≠ h),
          logarithmicThirdCorrelationBound t A N r s
            (finiteShiftDistance h k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact padded_logarithmicSecondDifference_correlation_norm_le
            t A r s N H h k ht hA hH hNArs hr hs
              (Finset.mem_range.mp hh)
              (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
              (Ne.symm (Finset.mem_filter.mp hk).2)
      _ ≤ 2 * ∑ q ∈ Finset.Icc 1 (H - 1),
          logarithmicThirdCorrelationBound t A N r s q :=
        sum_shiftDistance_le_two_mul_sum
          (fun q => logarithmicThirdCorrelationBound t A N r s q)
          (fun q => logarithmicThirdCorrelationBound_nonneg
            t A N r s q ht hA hr hs) (Finset.mem_range.mp hh)

#print axioms logarithmicThirdDifference_B_process
#print axioms padded_logarithmicSecondDifference_correlation_eq
#print axioms logarithmicSecondDifference_weyl_AB_process

end

end GafniTao
