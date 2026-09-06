import GafniTao.ClassicalA3BMiddleMajorants

/-!
# The outer square-root majorant in `A³B`

This module converts the middle squared estimate into four explicit radical
terms.  The final term still carries the first-shift decay needed by the
outermost finite averaging.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicDifferenceA3SquaredMajorant
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) : ℝ :=
  2 * (N : ℝ) ^ 2 / H₂ +
    8 * (N : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ) +
    412 * (N : ℝ) ^ 2 *
      Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)) +
    584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
      Real.sqrt (1 /
        (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5))) *
      (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))

theorem logarithmicDifference_A3_compact_eq_squaredMajorant
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) (hH₂ : 0 < H₂) :
    (2 * (N : ℝ) / H₂) *
        ((N : ℝ) +
          2 * logarithmicA3MiddleInnerSumBound t A N H₁ H₂ H₃ r) =
      logarithmicDifferenceA3SquaredMajorant t A N H₁ H₂ H₃ r := by
  unfold logarithmicA3MiddleInnerSumBound
    logarithmicDifferenceA3SquaredMajorant
  field_simp [show (H₂ : ℝ) ≠ 0 by exact_mod_cast hH₂.ne']
  ring

noncomputable def logarithmicDifferenceA3RawNormBound
    (t A : ℝ) (N H₁ H₂ H₃ r : ℕ) : ℝ :=
  Real.sqrt (2 * (N : ℝ) ^ 2 / H₂) +
    Real.sqrt (8 * (N : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)) +
    Real.sqrt (412 * (N : ℝ) ^ 2 *
      Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5))) +
    Real.sqrt (584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
      Real.sqrt (1 /
        (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5))) *
      (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ))))

private theorem sqrt_four_sum_le
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a + b + c + d) ≤
      Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d := by
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hsqc := Real.sq_sqrt hc
  have hsqd := Real.sq_sqrt hd
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      Real.sqrt_nonneg c, Real.sqrt_nonneg d]

theorem norm_logarithmicDifference_sum_le_A3_raw
    (t A : ℝ) (r N H₁ H₂ H₃ : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hrHigh : r ≤ H₁)
    (hNAr : (N : ℝ) + r ≤ A) (hH₂pos : 0 < H₂) (hH₂ : H₂ ≤ N)
    (hH₃pos : 0 < H₃) (hH₃ : H₃ ≤ N - (H₂ - 1))
    (hsmall : t * (H₁ : ℝ) * (H₂ : ℝ) * (H₃ : ℝ) / A ^ 5 ≤ 1) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
        integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ≤
      logarithmicDifferenceA3RawNormBound t A N H₁ H₂ H₃ r := by
  have hsq := norm_logarithmicDifference_sum_sq_le_A3_compact
    t A r N H₁ H₂ H₃ ht hA hr hrHigh hNAr hH₂pos hH₂
      hH₃pos hH₃ hsmall
  rw [logarithmicDifference_A3_compact_eq_squaredMajorant
    t A N H₁ H₂ H₃ r hH₂pos] at hsq
  let a : ℝ := 2 * (N : ℝ) ^ 2 / H₂
  let b : ℝ := 8 * (N : ℝ) ^ 2 / Real.sqrt (H₃ : ℝ)
  let c : ℝ := 412 * (N : ℝ) ^ 2 *
    Real.sqrt (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5))
  let d : ℝ := 584 * (N : ℝ) * Real.sqrt (N : ℝ) / H₂ *
    Real.sqrt (1 /
      (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r / A ^ 5))) *
    (Real.sqrt (H₂ : ℝ) * Real.sqrt (2 * Real.sqrt (H₂ : ℝ)))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hsqrt :
      ‖∑ n ∈ Finset.Ico (0 : ℤ) N,
        integerPhaseTerm (logarithmicDifferencePhase t A 0 r) n‖ ≤
        Real.sqrt (a + b + c + d) := Real.le_sqrt_of_sq_le (by
          simpa only [logarithmicDifferenceA3SquaredMajorant, a, b, c, d]
            using hsq)
  calc
    _ ≤ Real.sqrt (a + b + c + d) := hsqrt
    _ ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d :=
      sqrt_four_sum_le ha hb hc hd
    _ = logarithmicDifferenceA3RawNormBound t A N H₁ H₂ H₃ r := by
      rfl

theorem separated_A3_outer_inverse_factor
    (t A : ℝ) (H r : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH : 0 < H) (hr : 0 < r) :
    Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 5))) =
      Real.sqrt (1 /
        (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 5))) *
        Real.sqrt (1 / Real.sqrt (r : ℝ)) := by
  have hbase : 0 < t / A ^ 5 := by positivity
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have hsH : 0 < Real.sqrt (H : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hH)
  have hsbase : 0 < Real.sqrt (t / A ^ 5) := Real.sqrt_pos.2 hbase
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrReal
  have hsplit : Real.sqrt (t * (r : ℝ) / A ^ 5) =
      Real.sqrt (t / A ^ 5) * Real.sqrt (r : ℝ) := by
    rw [show t * (r : ℝ) / A ^ 5 = (t / A ^ 5) * r by ring,
      Real.sqrt_mul hbase.le]
  have hrecip :
      1 / (Real.sqrt (H : ℝ) * Real.sqrt (t * r / A ^ 5)) =
        (1 / (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 5))) *
          (1 / Real.sqrt (r : ℝ)) := by
    rw [hsplit]
    field_simp [hsH.ne', hsbase.ne', hsr.ne']
  rw [hrecip, Real.sqrt_mul (by positivity :
    0 ≤ 1 / (Real.sqrt (H : ℝ) * Real.sqrt (t / A ^ 5)))]

theorem sum_Icc_eighth_root_le (H : ℕ) :
    ∑ r ∈ Finset.Icc 1 (H - 1),
        Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) ≤
      Real.sqrt (H : ℝ) *
        Real.sqrt (Real.sqrt (H : ℝ) *
          Real.sqrt (2 * Real.sqrt (H : ℝ))) := by
  let S := Finset.Icc 1 (H - 1)
  have hcard : (S.card : ℝ) ≤ H := by
    have hsubset : S ⊆ Finset.range H := by
      intro r hr
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hr
        omega)
    have hc : S.card ≤ H := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    exact_mod_cast hc
  have hsum : ∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ)) ≤
      Real.sqrt (H : ℝ) * Real.sqrt (2 * Real.sqrt (H : ℝ)) := by
    simpa only [S] using sum_Icc_sqrt_one_div_sqrt_le H
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun _r : ℕ => (1 : ℝ))
    (fun r : ℕ => Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))))
  have hsquares :
      ∑ r ∈ S, (Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ)))) ^ 2 =
        ∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ)) := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [Real.sq_sqrt]
    positivity
  have honeSquares : ∑ _r ∈ S, (1 : ℝ) ^ 2 = S.card := by simp
  have hraw :
      ∑ r ∈ S, Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) ≤
        Real.sqrt (S.card : ℝ) *
          Real.sqrt (∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ))) := by
    simpa only [one_mul, honeSquares, hsquares] using hcs
  calc
    ∑ r ∈ Finset.Icc 1 (H - 1),
        Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) =
      ∑ r ∈ S, Real.sqrt (Real.sqrt (1 / Real.sqrt (r : ℝ))) := by rfl
    _ ≤ Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ r ∈ S, Real.sqrt (1 / Real.sqrt (r : ℝ))) := hraw
    _ ≤ Real.sqrt (H : ℝ) *
        Real.sqrt (Real.sqrt (H : ℝ) *
          Real.sqrt (2 * Real.sqrt (H : ℝ))) := by gcongr

#print axioms logarithmicDifference_A3_compact_eq_squaredMajorant
#print axioms norm_logarithmicDifference_sum_le_A3_raw
#print axioms separated_A3_outer_inverse_factor
#print axioms sum_Icc_eighth_root_le

end

end GafniTao
