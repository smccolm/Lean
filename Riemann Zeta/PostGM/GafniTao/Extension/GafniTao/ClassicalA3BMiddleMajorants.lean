import GafniTao.ClassicalA3BMiddle

/-!
# Summation at the middle `A` stage of `A³B`

The inverse-curvature term is kept as `s⁻¹/4`; this is essential for the
classical exponent and is discharged by a finite Cauchy--Schwarz estimate.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem separated_A3_second_inverse_factor
    (t A : ℝ) (H r s : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : 0 < H) (hr : 0 < r) (hs : 0 < s) :
    Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t * r * s / A ^ 5))) =
      Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 5))) *
        Real.sqrt (1 / Real.sqrt (s : ℝ)) := by
  have hbase : 0 < t * (r : ℝ) / A ^ 5 := by positivity
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsH : 0 < Real.sqrt (H : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hH)
  have hsbase : 0 < Real.sqrt (t * (r : ℝ) / A ^ 5) :=
    Real.sqrt_pos.2 hbase
  have hss : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hsReal
  have hsplit : Real.sqrt (t * (r : ℝ) * s / A ^ 5) =
      Real.sqrt (t * (r : ℝ) / A ^ 5) * Real.sqrt (s : ℝ) := by
    rw [show t * (r : ℝ) * s / A ^ 5 =
      (t * (r : ℝ) / A ^ 5) * s by ring, Real.sqrt_mul hbase.le]
  have hrecip :
      1 / (Real.sqrt (H : ℝ) * Real.sqrt (t * r * s / A ^ 5)) =
        (1 / (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 5))) *
          (1 / Real.sqrt (s : ℝ)) := by
    rw [hsplit]
    field_simp [hsH.ne', hsbase.ne', hss.ne']
  rw [hrecip, Real.sqrt_mul (by positivity :
    0 ≤ 1 / (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 5)))]

noncomputable def logarithmicA3MiddleInnerSumBound
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) : ℝ :=
  (H₂ : ℝ) *
      (2 * N / Real.sqrt (H₃ : ℝ) +
        103 * N * Real.sqrt
          (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5))) +
    146 * Real.sqrt (N : ℝ) *
      Real.sqrt (1 /
        (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5))) *
      (Real.sqrt (H₂ : ℝ) *
        Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))

theorem sum_logarithmicSecondDifferenceA3SeparatedBound_le
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₃ : 0 < H₃) (hr : 0 < r) :
    ∑ s ∈ Finset.Icc 1 (H₂ - 1),
        logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s ≤
      logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r := by
  let S := Finset.Icc 1 (H₂ - 1)
  let d : ℝ := 2 * N / Real.sqrt (H₃ : ℝ) +
    103 * N * Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5))
  let e : ℝ := 146 * Real.sqrt (N : ℝ) *
    Real.sqrt (1 /
      (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5)))
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hcard : (S.card : ℝ) ≤ H₂ := by
    have hsubset : S ⊆ Finset.range H₂ := by
      intro s hs
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hs
        omega)
    have hc : S.card ≤ H₂ := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    exact_mod_cast hc
  have hquarter : ∑ s ∈ S,
      Real.sqrt (1 / Real.sqrt (s : ℝ)) ≤
        Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)) := by
    simpa only [S] using sum_Icc_sqrt_one_div_sqrt_le H₂
  have hpoint : ∀ s ∈ S,
      logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s =
        d + e * Real.sqrt (1 / Real.sqrt (s : ℝ)) := by
    intro s hsMem
    have hsPos : 0 < s := by
      have := Finset.mem_Icc.mp hsMem
      omega
    unfold logarithmicSecondDifferenceA3SeparatedBound
    rw [separated_A3_second_inverse_factor t A H₃ r s ht hA hH₃ hr hsPos]
    dsimp only [d, e]
    ring
  calc
    ∑ s ∈ Finset.Icc 1 (H₂ - 1),
        logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s =
      ∑ s ∈ S, (d + e * Real.sqrt (1 / Real.sqrt (s : ℝ))) := by
        apply Finset.sum_congr rfl
        intro s hsMem
        exact hpoint s hsMem
    _ = (S.card : ℝ) * d + e *
        (∑ s ∈ S, Real.sqrt (1 / Real.sqrt (s : ℝ))) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Finset.mul_sum]
    _ ≤ (H₂ : ℝ) * d + e *
        (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hcard hd)
        (mul_le_mul_of_nonneg_left hquarter he)
    _ = logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r := by
      unfold logarithmicA3MiddleInnerSumBound
      dsimp only [d, e]

theorem logarithmicA3SecondCorrelationBound_le_separated
    (t A : ℝ) (N H₁ H₂ H₃ r s : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hrHigh : r ≤ H₁) (hsHigh : s ≤ H₂ - 1)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    logarithmicA3SecondCorrelationBound t A N r H₃ s ≤
      logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s := by
  unfold logarithmicA3SecondCorrelationBound
  have hH₃s : H₃ ≤ N - s := by omega
  have hsH₂ : s ≤ H₂ := hsHigh.trans (Nat.sub_le H₂ 1)
  have hsmallRS : t * (r : ℝ) * (s : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1 := by
    calc
      t * (r : ℝ) * (s : ℝ) * (H₃ : ℝ) / A ^ 5 ≤
          t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 := by
            gcongr
      _ ≤ 1 := hsmall
  exact (logarithmicSecondDifferenceA3Bound_le_raw
    t A r s (N - s) H₃ ht hA hr hs hH₃pos hH₃s hsmallRS).trans
      (logarithmicSecondDifferenceA3RawBound_le_separated
        t A N H₁ H₂ H₃ r s ht hA hH₃pos hr hs hrHigh
          hsH₂)

theorem sum_logarithmicA3SecondCorrelationBound_le
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hrHigh : r ≤ H₁)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    ∑ s ∈ Finset.Icc 1 (H₂ - 1),
        logarithmicA3SecondCorrelationBound t A N r H₃ s ≤
      logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r := by
  calc
    ∑ s ∈ Finset.Icc 1 (H₂ - 1),
        logarithmicA3SecondCorrelationBound t A N r H₃ s ≤
      ∑ s ∈ Finset.Icc 1 (H₂ - 1),
        logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s := by
      apply Finset.sum_le_sum
      intro s hsMem
      have hsData := Finset.mem_Icc.mp hsMem
      exact logarithmicA3SecondCorrelationBound_le_separated
        t A N H₁ H₂ H₃ r s ht hA hr (by omega) hrHigh hsData.2
          hH₃pos hH₃ hsmall
    _ ≤ logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r :=
      sum_logarithmicSecondDifferenceA3SeparatedBound_le
        t A N H₁ H₂ H₃ r ht hA hH₃pos hr

theorem logarithmicDifference_weyl_A2B_process_A3_summed
    (t A : ℝ) (r N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hrHigh : r ≤ H₁)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    (H₂ : ℝ) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
          integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ^ 2 ≤
      ((N + H₂ : ℕ) : ℝ) *
        ((H₂ : ℝ) * N + (H₂ : ℝ) *
          (2 * logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r)) := by
  have hraw := logarithmicDifference_weyl_A2B_process_A3
    t A r N H₂ H₃ ht hA hr hNAr hH₂ hH₃pos hH₃
  refine hraw.trans ?_
  have hsum := sum_logarithmicA3SecondCorrelationBound_le
    t A N H₁ H₂ H₃ r ht hA hr hrHigh hH₃pos hH₃ hsmall
  gcongr

theorem logarithmicA3MiddleInnerSumBound_nonneg
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) :
    0 ≤ logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r := by
  unfold logarithmicA3MiddleInnerSumBound
  positivity

theorem norm_logarithmicDifference_sum_sq_le_A3_compact
    (t A : ℝ) (r N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hrHigh : r ≤ H₁)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂pos : 0 < H₂) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
        integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ^ 2 ≤
      (2 * (N : ℝ) / H₂) *
        ((N : ℝ) +
          2 * logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r) := by
  have hsource := logarithmicDifference_weyl_A2B_process_A3_summed
    t A r N H₁ H₂ H₃ ht hA hr hrHigh hNAr hH₂ hH₃pos hH₃ hsmall
  let S := logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r
  have hS : 0 ≤ S := logarithmicA3MiddleInnerSumBound_nonneg t A N H₁ H₂ H₃ r
  have hNH : ((N + H₂ : ℕ) : ℝ) ≤ 2 * N := by
    norm_num
    exact_mod_cast (by omega : N + H₂ ≤ 2 * N)
  have hH₂R : (0 : ℝ) < H₂ := by exact_mod_cast hH₂pos
  have hupper :
      ((N + H₂ : ℕ) : ℝ) *
          ((H₂ : ℝ) * N + (H₂ : ℝ) * (2 * S)) ≤
        (H₂ : ℝ) ^ 2 *
          ((2 * (N : ℝ) / H₂) * ((N : ℝ) + 2 * S)) := by
    calc
      _ ≤ (2 * (N : ℝ)) *
          ((H₂ : ℝ) * N + (H₂ : ℝ) * (2 * S)) := by gcongr
      _ = (H₂ : ℝ) ^ 2 *
          ((2 * (N : ℝ) / H₂) * ((N : ℝ) + 2 * S)) := by
        field_simp [hH₂R.ne']
  have hsq := hsource.trans (by simpa only [S] using hupper)
  apply le_of_mul_le_mul_left (by simpa [mul_assoc] using hsq)
  exact sq_pos_of_pos hH₂R

#print axioms separated_A3_second_inverse_factor
#print axioms sum_logarithmicA3SecondCorrelationBound_le
#print axioms logarithmicDifference_weyl_A2B_process_A3_summed
#print axioms norm_logarithmicDifference_sum_sq_le_A3_compact

end

end GafniTao
