import GafniTao.HeathBrownAtkinsonSourcePhysical

/-!
# The literal harmonic loss in Ivić equation (7.25)

The Bombieri--Halász row estimate contains the exact natural harmonic number
`harmonic ⌈J / G⌉₊`.  On the physical range `J / G ≤ T`, this file replaces
that term by an explicit multiple of `log T`.  Both the natural ceiling and
the scale relation remain hypotheses of the public theorem, so the source's
logarithmic loss is not inserted by an informal big-O simplification.
-/

namespace GafniTao

noncomputable section

/-- The ceiling in the scaled reciprocal-distance sum costs at most the
explicit factor `4` on the source range `2 ≤ T` and `J / G ≤ T`. -/
theorem harmonic_ceil_div_le_four_log
    {T G J : ℝ} (hT : 2 ≤ T) (hG : 0 < G) (hJ : 0 ≤ J)
    (hJG : J / G ≤ T) :
    (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) ≤ 4 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hratio0 : 0 ≤ J / G := div_nonneg hJ hG.le
  have hceilRaw : ((⌈J / G⌉₊ : ℕ) : ℝ) < J / G + 1 :=
    Nat.ceil_lt_add_one hratio0
  have hceilUpper : ((⌈J / G⌉₊ : ℕ) : ℝ) ≤ 2 * T := by
    linarith
  have hHarmonic :
      (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) ≤
        1 + Real.log (⌈J / G⌉₊ : ℕ) :=
    harmonic_le_one_add_log ⌈J / G⌉₊
  have hlogCeil :
      Real.log (⌈J / G⌉₊ : ℕ) ≤ Real.log (2 * T) := by
    by_cases hceil : ⌈J / G⌉₊ = 0
    · simp [hceil, Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * T)]
    · exact Real.log_le_log
        (by exact_mod_cast (Nat.pos_of_ne_zero hceil)) hceilUpper
  have hlogMul : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hTpos.ne']
  have hlogT : Real.log 2 ≤ Real.log T :=
    Real.log_le_log (by norm_num) hT
  have hone : 1 ≤ 2 * Real.log T := by
    have hlogTwo : (1 : ℝ) / 2 < Real.log 2 :=
      (by norm_num : (1 : ℝ) / 2 < 0.6931471803) |>.trans
        Real.log_two_gt_d9
    linarith
  calc
    (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) ≤
        1 + Real.log (⌈J / G⌉₊ : ℕ) := hHarmonic
    _ ≤ 1 + Real.log (2 * T) := by linarith
    _ = 1 + Real.log 2 + Real.log T := by rw [hlogMul]; ring
    _ ≤ 4 * Real.log T := by linarith

/-- The reciprocal-gap row contribution in the source Lemma 7.1, with the
literal harmonic factor discharged and every numerical coefficient shown. -/
theorem heathBrownAtkinsonSourceReciprocalContribution_le_log
    {T G J : ℝ} {K : ℕ} (hT : 2 ≤ T) (hG : 0 < G) (hJ : 0 ≤ J)
    (hJG : J / G ≤ T) :
    heathBrownAtkinsonSourceReciprocalContribution T G J K ≤
      224 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) / G * Real.log T := by
  have hH := harmonic_ceil_div_le_four_log hT hG hJ hJG
  have hsqrt : 0 ≤ Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) :=
    Real.sqrt_nonneg _
  have htwoG : 0 ≤ 2 / G := div_nonneg (by norm_num) hG.le
  unfold heathBrownAtkinsonSourceReciprocalContribution
    heathBrownAtkinsonEquation719ReciprocalCoefficient
  calc
    28 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) *
          ((2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ))) ≤
        28 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) *
          ((2 / G) * (4 * Real.log T)) := by gcongr
    _ = 224 * Real.sqrt (T * ((K + 1 : ℕ) : ℝ)) / G *
          Real.log T := by ring


end

end GafniTao
