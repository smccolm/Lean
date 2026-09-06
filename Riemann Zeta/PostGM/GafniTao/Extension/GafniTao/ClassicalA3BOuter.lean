import GafniTao.ClassicalA3BOuterMajorants
import GafniTao.ClassicalA2BOuter

/-!
# Complete finite outer `A` process for `A³B`

This file connects the three nested difference estimates back to the original
logarithmic exponential block.  In particular, the public bound below consumes
the actual finite correlations rather than an exponent-pair certificate.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicA3BCorrelationBound
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) : ℝ :=
  logarithmicDifferenceA3RawNormBound t A (N - r) H₁ H₂ H₃ r

theorem logarithmicA3BCorrelationBound_nonneg
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) :
    0 ≤ logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r := by
  unfold logarithmicA3BCorrelationBound logarithmicDifferenceA3RawNormBound
  positivity

theorem padded_logarithmic_correlation_norm_le_A3_of_lt
    (t A : ℝ) (N H₁ H₂ H₃ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₃pos : 0 < H₃)
    (hH₃ : H₃ ≤ N - (H₁ - 1) - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1)
    (hh : h < H₁) (hk : k < H₁) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
      logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ (k - h) := by
  have hr : 0 < k - h := Nat.sub_pos_of_lt hhk
  have hrHigh : k - h ≤ H₁ - 1 := by omega
  have hrN : k - h ≤ N := hrHigh.trans ((Nat.sub_le H₁ 1).trans hH₁)
  have hH₂' : H₂ ≤ N - (k - h) := by omega
  have hH₃' : H₃ ≤ (N - (k - h)) - (H₂ - 1) := by omega
  have hsize : (((N - (k - h) : ℕ) : ℝ)) + (((k - h : ℕ) : ℝ)) ≤ A := by
    calc
      (((N - (k - h) : ℕ) : ℝ)) + (((k - h : ℕ) : ℝ)) = (N : ℝ) := by
        rw [Nat.cast_sub hrN]
        ring
      _ ≤ A := hNA
  rw [padded_logarithmic_correlation_eq t A N H₁ h k hh hk hhk,
    norm_star, ← integerPhaseSum_eq_range]
  exact norm_logarithmicDifference_sum_le_A3_raw
    t A (k - h) (N - (k - h)) H₁ H₂ H₃ ht hA hr
      (hrHigh.trans (Nat.sub_le H₁ 1)) hsize hH₂pos hH₂'
      hH₃pos hH₃' hsmall

theorem padded_logarithmic_correlation_norm_le_A3
    (t A : ℝ) (N H₁ H₂ H₃ h k : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₃pos : 0 < H₃)
    (hH₃ : H₃ ≤ N - (H₁ - 1) - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1)
    (hh : h < H₁) (hk : k < H₁) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
      logarithmicA3BCorrelationBound t A N H₁ H₂ H₃
        (finiteShiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmic_correlation_norm_le_A3_of_lt
      t A N H₁ H₂ H₃ h k ht hA hNA hH₁ hH₂pos hH₃pos hH₃
        hsmall hh hk hhk
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hhk.le,
      zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmic_correlation_norm_le_A3_of_lt
      t A N H₁ H₂ H₃ k h ht hA hNA hH₁ hH₂pos hH₃pos hH₃
        hsmall hk hh hkh
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
    simpa only [finiteShiftDistance, Nat.sub_eq_zero_of_le hkh.le,
      add_zero] using hb

theorem logarithmic_weyl_A3B_process_raw
    (t A : ℝ) (N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂)
    (hH₃pos : 0 < H₃)
    (hH₃ : H₃ ≤ N - (H₁ - 1) - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    (H₁ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerLogarithmicTerm t A n‖ ^ 2 ≤
      ((N + H₁ : ℕ) : ℝ) *
        ((H₁ : ℝ) * N + (H₁ : ℝ) *
          (2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
            logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r)) := by
  apply interval_weyl_differencing_row_complex
    (integerLogarithmicTerm t A) N H₁
    (2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
      logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r)
  · intro n _hn
    simp
  · intro h hh
    calc
      ∑ k ∈ (Finset.range H₁).filter (fun k => k ≠ h),
          ‖∑ n ∈ Finset.Ico (-(H₁ : ℤ)) N,
            star (paddedShift (integerLogarithmicTerm t A) N n h) *
              paddedShift (integerLogarithmicTerm t A) N n k‖ ≤
        ∑ k ∈ (Finset.range H₁).filter (fun k => k ≠ h),
          logarithmicA3BCorrelationBound t A N H₁ H₂ H₃
            (finiteShiftDistance h k) := by
          apply Finset.sum_le_sum
          intro k hk
          exact padded_logarithmic_correlation_norm_le_A3
            t A N H₁ H₂ H₃ h k ht hA hNA hH₁ hH₂pos hH₃pos hH₃
              hsmall (Finset.mem_range.mp hh)
              (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
              (Ne.symm (Finset.mem_filter.mp hk).2)
      _ ≤ 2 * ∑ r ∈ Finset.Icc 1 (H₁ - 1),
          logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r :=
        sum_shiftDistance_le_two_mul_sum
          (fun r => logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r)
          (fun r => logarithmicA3BCorrelationBound_nonneg
            t A N H₁ H₂ H₃ r) (Finset.mem_range.mp hh)

theorem logarithmicA3BCorrelationBound_le_uniform_raw
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) :
    logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r ≤
      logarithmicDifferenceA3RawNormBound t A N H₁ H₂ H₃ r := by
  have hsub : (((N - r : ℕ) : ℝ)) ≤ N := by
    exact_mod_cast Nat.sub_le N r
  have hsubsq : (((N - r : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((N - r : ℕ) : ℝ)), sq_nonneg (N : ℝ)]
  have hsqrtSub : Real.sqrt (((N - r : ℕ) : ℝ)) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt hsub
  unfold logarithmicA3BCorrelationBound logarithmicDifferenceA3RawNormBound
  gcongr

noncomputable def logarithmicA3BOuterSumBound
    (t A : ℝ) (N H₁ H₂ H₃ : ℕ) : ℝ :=
  (H₁ : ℝ) *
      (Real.sqrt (2 * (N : ℝ) ^ 2 / H₂) +
        Real.sqrt (8 * (N : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)) +
        Real.sqrt (412 * (N : ℝ) ^ 2 *
          Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)))) +
    Real.sqrt (584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
      Real.sqrt (1 /
        (Real.sqrt (H₃ : ℝ) * Real.sqrt (t / A ^ 5))) *
      (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))) *
      (Real.sqrt (H₁ : ℝ) *
        Real.sqrt (Real.sqrt (H₁ : ℝ) *
          Real.sqrt (2 * Real.sqrt (H₁ : ℝ))))

theorem A3_outer_last_term_factor
    (t A : ℝ) (N H₂ H₃ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₃ : 0 < H₃) (hr : 0 < r) :
    Real.sqrt (584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
        Real.sqrt (1 /
          (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5))) *
        (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))) =
      Real.sqrt (584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
        Real.sqrt (1 /
          (Real.sqrt (H₃ : ℝ) * Real.sqrt (t / A ^ 5))) *
        (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))) *
      Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) := by
  rw [separated_A3_outer_inverse_factor t A H₃ r ht hA hH₃ hr]
  let C : ℝ := 584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
    Real.sqrt (1 /
      (Real.sqrt (H₃ : ℝ) * Real.sqrt (t / A ^ 5))) *
    (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))
  let u : ℝ := Real.sqrt (1 / Real.sqrt (r : ℝ))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hinside :
      584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
          (Real.sqrt (1 /
            (Real.sqrt (H₃ : ℝ) * Real.sqrt (t / A ^ 5))) *
            Real.sqrt (1 / Real.sqrt (r : ℝ))) *
          (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ))) =
        C * u := by
    dsimp only [C, u]
    ring
  rw [hinside]
  change Real.sqrt (C * u) = Real.sqrt C * Real.sqrt u
  exact Real.sqrt_mul hC u

theorem sum_logarithmicA3BCorrelationBound_le
    (t A : ℝ) (N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₃ : 0 < H₃) :
    ∑ r ∈ Finset.Icc 1 (H₁ - 1),
        logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r ≤
      logarithmicA3BOuterSumBound t A N H₁ H₂ H₃ := by
  let S := Finset.Icc 1 (H₁ - 1)
  let d : ℝ := Real.sqrt (2 * (N : ℝ) ^ 2 / H₂) +
    Real.sqrt (8 * (N : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)) +
    Real.sqrt (412 * (N : ℝ) ^ 2 *
      Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)))
  let e : ℝ := Real.sqrt (584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
    Real.sqrt (1 /
      (Real.sqrt (H₃ : ℝ) * Real.sqrt (t / A ^ 5))) *
    (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ))))
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hcard : (S.card : ℝ) ≤ H₁ := by
    have hsubset : S ⊆ Finset.range H₁ := by
      intro r hr
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hr
        omega)
    have hc : S.card ≤ H₁ := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    exact_mod_cast hc
  have heighth := sum_Icc_eighth_root_le H₁
  have hpoint : ∀ r ∈ S,
      logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r ≤
        d + e * Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) := by
    intro r hrMem
    have hr : 0 < r := by
      have := Finset.mem_Icc.mp hrMem
      omega
    have hu := logarithmicA3BCorrelationBound_le_uniform_raw
      t A N H₁ H₂ H₃ r
    unfold logarithmicDifferenceA3RawNormBound at hu
    rw [A3_outer_last_term_factor t A N H₂ H₃ r ht hA hH₃ hr] at hu
    simpa only [d, e] using hu
  calc
    ∑ r ∈ Finset.Icc 1 (H₁ - 1),
        logarithmicA3BCorrelationBound t A N H₁ H₂ H₃ r ≤
      ∑ r ∈ S, (d + e * Real.sqrt
        (Real.sqrt (1 / Real.sqrt (r : ℝ)))) := by
          simpa only [S] using Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * d + e *
        (∑ r ∈ S, Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ)))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Finset.mul_sum]
    _ ≤ (H₁ : ℝ) * d + e *
        (Real.sqrt (H₁ : ℝ) *
          Real.sqrt (Real.sqrt (H₁ : ℝ) *
            Real.sqrt (2 * Real.sqrt (H₁ : ℝ)))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hcard hd)
        (mul_le_mul_of_nonneg_left (by simpa only [S] using heighth) he)
    _ = logarithmicA3BOuterSumBound t A N H₁ H₂ H₃ := by
      unfold logarithmicA3BOuterSumBound
      dsimp only [d, e]

theorem logarithmic_weyl_A3B_process_summed
    (t A : ℝ) (N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hNA : (N : ℝ) ≤ A)
    (hH₁ : H₁ ≤ N) (hH₂pos : 0 < H₂) (hH₃pos : 0 < H₃)
    (hH₃ : H₃ ≤ N - (H₁ - 1) - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    (H₁ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerLogarithmicTerm t A n‖ ^ 2 ≤
      ((N + H₁ : ℕ) : ℝ) *
        ((H₁ : ℝ) * N + (H₁ : ℝ) *
          (2 * logarithmicA3BOuterSumBound t A N H₁ H₂ H₃)) := by
  have hraw := logarithmic_weyl_A3B_process_raw
    t A N H₁ H₂ H₃ ht hA hNA hH₁ hH₂pos hH₃pos hH₃ hsmall
  have hsum := sum_logarithmicA3BCorrelationBound_le
    t A N H₁ H₂ H₃ ht hA hH₃pos
  exact hraw.trans (by gcongr)

#print axioms logarithmicA3BCorrelationBound_le_uniform_raw
#print axioms A3_outer_last_term_factor
#print axioms sum_logarithmicA3BCorrelationBound_le
#print axioms logarithmic_weyl_A3B_process_summed

#print axioms padded_logarithmic_correlation_norm_le_A3_of_lt
#print axioms logarithmic_weyl_A3B_process_raw

end

end GafniTao
