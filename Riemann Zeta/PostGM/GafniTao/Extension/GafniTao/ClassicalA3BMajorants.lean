import GafniTao.ClassicalA3BInner
import GafniTao.ClassicalA2BMajorants

/-!
# Algebraic majorants for the innermost stage of `A³B`

This file removes the analytic `B`-process expression from the third
logarithmic difference and sums its exact finite correlation majorant over
the third shift.  No exponent-pair assertion is assumed here.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem logarithmicThirdCorrelationBound_le_homogeneous
    (t A : ℝ) (N r s q : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q) :
    logarithmicThirdCorrelationBound t A N r s q ≤
      1320 *
        ((N : ℝ) * Real.sqrt (t * r * s * q / A ^ 5) +
          (N : ℝ) * (t * r * s * q / A ^ 5) +
          1 / Real.sqrt (t * r * s * q / A ^ 5) + 1) := by
  let z : ℝ := t * r * s * q / A ^ 5
  have hz : 0 < z := by dsimp only [z]; positivity
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hszSq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz.le
  have hsqrt16 : Real.sqrt (z / 16) = Real.sqrt z / 4 :=
    sqrt_div_sixteen hz.le
  let M := N - q - 1
  have hMN : (M : ℝ) ≤ N := by
    exact_mod_cast (Nat.sub_le N (q + 1))
  have hfirst :
      (M : ℝ) * (192 * z) / (2 * Real.pi) + 2 ≤
        32 * (N : ℝ) * z + 2 := by
    have hden : 0 < 2 * Real.pi := by positivity
    rw [add_le_add_iff_right]
    have hMz : (M : ℝ) * z ≤ (N : ℝ) * z :=
      mul_le_mul_of_nonneg_right hMN hz.le
    have hcoef : 192 / (2 * Real.pi) ≤ (32 : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith [Real.pi_gt_three]
    calc
      (M : ℝ) * (192 * z) / (2 * Real.pi) =
          ((M : ℝ) * z) * (192 / (2 * Real.pi)) := by ring
      _ ≤ ((N : ℝ) * z) * 32 :=
        mul_le_mul hMz hcoef (by positivity) (by positivity)
      _ = 32 * (N : ℝ) * z := by ring
  have hsecond :
      2 * Real.pi / Real.sqrt (z / 16) +
          2 * (Real.sqrt (z / 16) / (z / 16) + 1) ≤
        40 / Real.sqrt z + 2 := by
    rw [hsqrt16]
    have hzNe : z ≠ 0 := hz.ne'
    have hszNe : Real.sqrt z ≠ 0 := hsz.ne'
    field_simp [hzNe, hszNe]
    nlinarith [Real.pi_lt_four]
  have hproduct := mul_le_mul hfirst hsecond
    (by positivity : 0 ≤
      2 * Real.pi / Real.sqrt (z / 16) +
        2 * (Real.sqrt (z / 16) / (z / 16) + 1))
    (by positivity : 0 ≤ 32 * (N : ℝ) * z + 2)
  have hsimple :
      (32 * (N : ℝ) * z + 2) * (40 / Real.sqrt z + 2) ≤
        1320 * ((N : ℝ) * Real.sqrt z +
          (N : ℝ) * z + 1 / Real.sqrt z + 1) := by
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hNz : 0 ≤ (N : ℝ) * z := mul_nonneg hN hz.le
    have hNzSqrt : 0 ≤ ((N : ℝ) * z) * Real.sqrt z :=
      mul_nonneg hNz hsz.le
    field_simp [hsz.ne']
    nlinarith
  have hzSixteen :
      t * (r : ℝ) * (s : ℝ) * (q : ℝ) / (16 * A ^ 5) = z / 16 := by
    dsimp only [z]
    field_simp [hA.ne']
  unfold logarithmicThirdCorrelationBound
  dsimp only
  rw [show 192 * t * (r : ℝ) * (s : ℝ) * (q : ℝ) / A ^ 5 =
      192 * z by dsimp only [z]; ring, hzSixteen]
  simpa only [z, M] using hproduct.trans hsimple

theorem logarithmicThirdCorrelationBound_le_simple
    (t A : ℝ) (N r s q : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hsmall : t * (r : ℝ) * (s : ℝ) * (q : ℝ) / A ^ 5 ≤ 1) :
    logarithmicThirdCorrelationBound t A N r s q ≤
      2640 * ((N : ℝ) * Real.sqrt (t * r * s * q / A ^ 5) +
        1 / Real.sqrt (t * r * s * q / A ^ 5)) := by
  let z : ℝ := t * r * s * q / A ^ 5
  have hz : 0 < z := by dsimp only [z]; positivity
  have hzOne : z ≤ 1 := by simpa only [z] using hsmall
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hszOne : Real.sqrt z ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hzOne
  have hzSqrt : z ≤ Real.sqrt z := by
    have hsq := Real.sq_sqrt hz.le
    nlinarith
  have honeInv : 1 ≤ 1 / Real.sqrt z := by
    rw [le_div_iff₀ hsz]
    simpa using hszOne
  have hraw := logarithmicThirdCorrelationBound_le_homogeneous
    t A N r s q ht hA hr hs hq
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  calc
    logarithmicThirdCorrelationBound t A N r s q ≤
        1320 * ((N : ℝ) * Real.sqrt z +
          (N : ℝ) * z + 1 / Real.sqrt z + 1) := by
      simpa only [z] using hraw
    _ ≤ 2640 * ((N : ℝ) * Real.sqrt z + 1 / Real.sqrt z) := by
      have hNz := mul_le_mul_of_nonneg_left hzSqrt hN
      nlinarith
    _ = 2640 * ((N : ℝ) * Real.sqrt (t * r * s * q / A ^ 5) +
        1 / Real.sqrt (t * r * s * q / A ^ 5)) := by rfl

theorem sum_logarithmicThirdCorrelationBound_le
    (t A : ℝ) (N r s H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hsmall : t * (r : ℝ) * (s : ℝ) * (H : ℝ) / A ^ 5 ≤ 1) :
    ∑ q ∈ Finset.Icc 1 (H - 1),
        logarithmicThirdCorrelationBound t A N r s q ≤
      2640 * ((N : ℝ) * H *
          Real.sqrt (t * r * s * H / A ^ 5) +
        2 * Real.sqrt (H : ℝ) /
          Real.sqrt (t * r * s / A ^ 5)) := by
  let z₀ : ℝ := t * r * s / A ^ 5
  have hz₀ : 0 < z₀ := by dsimp only [z₀]; positivity
  have hsz₀ : 0 < Real.sqrt z₀ := Real.sqrt_pos.2 hz₀
  have hzHEq : t * (r : ℝ) * (s : ℝ) * (H : ℝ) / A ^ 5 = z₀ * H := by
    dsimp only [z₀]
    ring
  let S := Finset.Icc 1 (H - 1)
  have hcard : (S.card : ℝ) ≤ H := by
    have hsubset : S ⊆ Finset.range H := by
      intro q hq
      exact Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hq
        omega)
    have hcardNat : S.card ≤ H := by
      simpa only [Finset.card_range] using Finset.card_le_card hsubset
    exact_mod_cast hcardNat
  have hpoint : ∀ q ∈ S,
      logarithmicThirdCorrelationBound t A N r s q ≤
        2640 * ((N : ℝ) * Real.sqrt (z₀ * H) +
          (1 / Real.sqrt z₀) * (1 / Real.sqrt (q : ℝ))) := by
    intro q hqMem
    have hqData := Finset.mem_Icc.mp hqMem
    have hqPos : 0 < q := by omega
    have hqH : q ≤ H := by omega
    have hzEq : t * (r : ℝ) * (s : ℝ) * (q : ℝ) / A ^ 5 = z₀ * q := by
      dsimp only [z₀]
      ring
    have hsmallQ : t * (r : ℝ) * (s : ℝ) * (q : ℝ) / A ^ 5 ≤ 1 := by
      calc
        t * (r : ℝ) * (s : ℝ) * (q : ℝ) / A ^ 5 ≤
            t * (r : ℝ) * (s : ℝ) * (H : ℝ) / A ^ 5 := by gcongr
        _ ≤ 1 := hsmall
    have hbase := logarithmicThirdCorrelationBound_le_simple
      t A N r s q ht hA hr hs hqPos hsmallQ
    have hsqrtLe : Real.sqrt (z₀ * q) ≤ Real.sqrt (z₀ * H) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqH) hz₀.le
    have hsqrtMul : Real.sqrt (z₀ * q) =
        Real.sqrt z₀ * Real.sqrt (q : ℝ) := by
      rw [Real.sqrt_mul hz₀.le]
    have hsqPos : 0 < Real.sqrt (q : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hqPos)
    have hinvEq : 1 / Real.sqrt (z₀ * q) =
        (1 / Real.sqrt z₀) * (1 / Real.sqrt (q : ℝ)) := by
      rw [hsqrtMul]
      field_simp [hsz₀.ne', hsqPos.ne']
    rw [hzEq] at hbase
    exact hbase.trans (by rw [hinvEq]; gcongr)
  calc
    ∑ q ∈ Finset.Icc 1 (H - 1),
        logarithmicThirdCorrelationBound t A N r s q ≤
      ∑ q ∈ S, 2640 * ((N : ℝ) * Real.sqrt (z₀ * H) +
        (1 / Real.sqrt z₀) * (1 / Real.sqrt (q : ℝ))) := by
          simpa only [S] using Finset.sum_le_sum hpoint
    _ = 2640 * ((S.card : ℝ) * ((N : ℝ) * Real.sqrt (z₀ * H)) +
        (1 / Real.sqrt z₀) *
          (∑ q ∈ S, 1 / Real.sqrt (q : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      congr 1
      · simp
      · rw [← Finset.mul_sum]
    _ ≤ 2640 * ((H : ℝ) * ((N : ℝ) * Real.sqrt (z₀ * H)) +
        (1 / Real.sqrt z₀) * (2 * Real.sqrt (H : ℝ))) := by
      have hsum : ∑ q ∈ S, 1 / Real.sqrt (q : ℝ) ≤
          2 * Real.sqrt (H : ℝ) := by
        simpa only [S] using sum_Icc_one_div_sqrt_le_two_sqrt H
      gcongr
    _ = 2640 * ((N : ℝ) * H *
          Real.sqrt (t * r * s * H / A ^ 5) +
        2 * Real.sqrt (H : ℝ) / Real.sqrt (t * r * s / A ^ 5)) := by
      rw [hzHEq, show t * (r : ℝ) * (s : ℝ) / A ^ 5 = z₀ by rfl]
      ring

noncomputable def logarithmicSecondDifferenceA3Majorant
    (t A : ℝ) (r s N H : ℕ) : ℝ :=
  ((N + H : ℕ) : ℝ) *
    ((H : ℝ) * N + (H : ℝ) *
      (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
        logarithmicThirdCorrelationBound t A N r s q))

noncomputable def logarithmicSecondDifferenceA3Bound
    (t A : ℝ) (r s N H : ℕ) : ℝ :=
  Real.sqrt (logarithmicSecondDifferenceA3Majorant t A r s N H) / H

theorem norm_logarithmicSecondDifferenceSum_le_A3Bound
    (t A : ℝ) (r s N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hHpos : 0 < H) (hH : H ≤ N)
    (hNArs : (N : ℝ) + r + s ≤ A) :
    ‖∑ n ∈ Finset.range N,
      unitaryPhase (logarithmicSecondDifferencePhase t A r s n)‖ ≤
      logarithmicSecondDifferenceA3Bound t A r s N H := by
  have hsquared := logarithmicSecondDifference_weyl_AB_process
    t A r s N H ht hA hr hs hH hNArs
  rw [integerPhaseSum_eq_range] at hsquared
  have hsq :
      (((H : ℝ) * ‖∑ n ∈ Finset.range N,
        unitaryPhase (logarithmicSecondDifferencePhase t A r s n)‖) ^ 2) ≤
        logarithmicSecondDifferenceA3Majorant t A r s N H := by
    unfold logarithmicSecondDifferenceA3Majorant
    nlinarith
  have hsqrt :
      (H : ℝ) * ‖∑ n ∈ Finset.range N,
        unitaryPhase (logarithmicSecondDifferencePhase t A r s n)‖ ≤
        Real.sqrt (logarithmicSecondDifferenceA3Majorant t A r s N H) :=
    Real.le_sqrt_of_sq_le hsq
  unfold logarithmicSecondDifferenceA3Bound
  rw [le_div_iff₀ (Nat.cast_pos.mpr hHpos)]
  simpa only [mul_comm] using hsqrt

theorem logarithmicSecondDifferenceA3Majorant_le_simple
    (t A : ℝ) (r s N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hH : H ≤ N)
    (hsmall : t * (r : ℝ) * (s : ℝ) * (H : ℝ) / A ^ 5 ≤ 1) :
    logarithmicSecondDifferenceA3Majorant t A r s N H ≤
      2 * (N : ℝ) * H *
        ((N : ℝ) + 5280 *
          ((N : ℝ) * H * Real.sqrt (t * r * s * H / A ^ 5) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r * s / A ^ 5))) := by
  have hsum := sum_logarithmicThirdCorrelationBound_le
    t A N r s H ht hA hr hs hsmall
  have hNH : ((N + H : ℕ) : ℝ) ≤ 2 * N := by
    norm_num
    exact_mod_cast (by omega : N + H ≤ 2 * N)
  have hinnerNonneg :
      0 ≤ (H : ℝ) * N + (H : ℝ) *
        (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
          logarithmicThirdCorrelationBound t A N r s q) := by
    apply add_nonneg
    · positivity
    · apply mul_nonneg (Nat.cast_nonneg H)
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg fun q hqMem =>
        logarithmicThirdCorrelationBound_nonneg t A N r s q ht hA hr hs
  unfold logarithmicSecondDifferenceA3Majorant
  calc
    ((N + H : ℕ) : ℝ) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
            logarithmicThirdCorrelationBound t A N r s q)) ≤
      (2 * (N : ℝ)) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * ∑ q ∈ Finset.Icc 1 (H - 1),
            logarithmicThirdCorrelationBound t A N r s q)) :=
      mul_le_mul_of_nonneg_right hNH hinnerNonneg
    _ ≤ (2 * (N : ℝ)) *
        ((H : ℝ) * N + (H : ℝ) *
          (2 * (2640 * ((N : ℝ) * H *
            Real.sqrt (t * r * s * H / A ^ 5) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r * s / A ^ 5))))) := by
      gcongr
    _ = 2 * (N : ℝ) * H *
        ((N : ℝ) + 5280 *
          ((N : ℝ) * H * Real.sqrt (t * r * s * H / A ^ 5) +
            2 * Real.sqrt (H : ℝ) /
              Real.sqrt (t * r * s / A ^ 5))) := by ring

noncomputable def logarithmicSecondDifferenceA3RawBound
    (t A : ℝ) (r s N H : ℕ) : ℝ :=
  Real.sqrt (2 * (N : ℝ) ^ 2 * H) / H +
    Real.sqrt (10560 * (N : ℝ) ^ 2 * H ^ 2 *
      Real.sqrt (t * r * s * H / A ^ 5)) / H +
    Real.sqrt (21120 * (N : ℝ) * H * Real.sqrt (H : ℝ) /
      Real.sqrt (t * r * s / A ^ 5)) / H

private theorem sqrt_three_sum_le_A3
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  have hsqa := Real.sq_sqrt ha
  have hsqb := Real.sq_sqrt hb
  have hsqc := Real.sq_sqrt hc
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c]

theorem logarithmicSecondDifferenceA3Bound_le_raw
    (t A : ℝ) (r s N H : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hHpos : 0 < H) (hH : H ≤ N)
    (hsmall : t * (r : ℝ) * (s : ℝ) * (H : ℝ) / A ^ 5 ≤ 1) :
    logarithmicSecondDifferenceA3Bound t A r s N H ≤
      logarithmicSecondDifferenceA3RawBound t A r s N H := by
  let a : ℝ := 2 * (N : ℝ) ^ 2 * H
  let b : ℝ := 10560 * (N : ℝ) ^ 2 * H ^ 2 *
    Real.sqrt (t * r * s * H / A ^ 5)
  let c : ℝ := 21120 * (N : ℝ) * H * Real.sqrt (H : ℝ) /
    Real.sqrt (t * r * s / A ^ 5)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmaj := logarithmicSecondDifferenceA3Majorant_le_simple
    t A r s N H ht hA hr hs hH hsmall
  have hrewrite :
      2 * (N : ℝ) * H *
          ((N : ℝ) + 5280 *
            ((N : ℝ) * H * Real.sqrt (t * r * s * H / A ^ 5) +
              2 * Real.sqrt (H : ℝ) /
                Real.sqrt (t * r * s / A ^ 5))) = a + b + c := by
    dsimp only [a, b, c]
    ring
  rw [hrewrite] at hmaj
  unfold logarithmicSecondDifferenceA3Bound
    logarithmicSecondDifferenceA3RawBound
  change Real.sqrt (logarithmicSecondDifferenceA3Majorant t A r s N H) / H ≤
    Real.sqrt a / H + Real.sqrt b / H + Real.sqrt c / H
  calc
    Real.sqrt (logarithmicSecondDifferenceA3Majorant t A r s N H) / H ≤
        Real.sqrt (a + b + c) / H := by gcongr
    _ ≤ (Real.sqrt a + Real.sqrt b + Real.sqrt c) / H := by
      gcongr
      exact sqrt_three_sum_le_A3 ha hb hc
    _ = Real.sqrt a / H + Real.sqrt b / H + Real.sqrt c / H := by ring

noncomputable def logarithmicSecondDifferenceA3SeparatedBound
    (t A : ℝ) (N H₁ H₂ H₃ r s : ℕ) : ℝ :=
  2 * N / Real.sqrt (H₃ : ℝ) +
    103 * N * Real.sqrt
      (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)) +
    146 * Real.sqrt (N : ℝ) *
      Real.sqrt (1 /
        (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r * s / A ^ 5)))

theorem logarithmicSecondDifferenceA3RawBound_le_separated
    (t A : ℝ) (N H₁ H₂ H₃ r s : ℕ)
    (ht : 0 < t) (hA : 0 < A) (hH₃pos : 0 < H₃)
    (hr : 0 < r) (hs : 0 < s) (hrHigh : r ≤ H₁) (hsHigh : s ≤ H₂) :
    logarithmicSecondDifferenceA3RawBound t A r s (N - s) H₃ ≤
      logarithmicSecondDifferenceA3SeparatedBound t A N H₁ H₂ H₃ r s := by
  have hsub : (((N - s : ℕ) : ℝ)) ≤ N := by
    have hsubNat : N - s ≤ N := by omega
    exact_mod_cast hsubNat
  have hsubsq : (((N - s : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((N - s : ℕ) : ℝ)), sq_nonneg (N : ℝ)]
  have hrs : (r : ℝ) * s ≤ (H₁ : ℝ) * H₂ := by gcongr
  have hH : (0 : ℝ) < H₃ := by exact_mod_cast hH₃pos
  have hsH : 0 < Real.sqrt (H₃ : ℝ) := Real.sqrt_pos.2 hH
  have hsHsq : Real.sqrt (H₃ : ℝ) ^ 2 = H₃ := Real.sq_sqrt hH.le
  have hbase : 0 < t * (r : ℝ) * s / A ^ 5 := by positivity
  have hsbase : 0 < Real.sqrt (t * (r : ℝ) * s / A ^ 5) :=
    Real.sqrt_pos.2 hbase
  unfold logarithmicSecondDifferenceA3RawBound
    logarithmicSecondDifferenceA3SeparatedBound
  have hfirst :
      Real.sqrt (2 * (((N - s : ℕ) : ℝ)) ^ 2 * H₃) / H₃ ≤
        2 * N / Real.sqrt (H₃ : ℝ) := by
    rw [div_le_iff₀ hH, Real.sqrt_le_iff]
    constructor
    · positivity
    · field_simp [hsH.ne']
      nlinarith [hsHsq]
  have hsqrtParam :
      Real.sqrt (t * (r : ℝ) * (s : ℝ) * H₃ / A ^ 5) ≤
        Real.sqrt (t * (H₁ : ℝ) * H₂ * H₃ / A ^ 5) := by
    apply Real.sqrt_le_sqrt
    gcongr
  have hsecond :
      Real.sqrt (10560 * (((N - s : ℕ) : ℝ)) ^ 2 * H₃ ^ 2 *
          Real.sqrt (t * r * s * H₃ / A ^ 5)) / H₃ ≤
        103 * N * Real.sqrt
          (Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)) := by
    rw [div_le_iff₀ hH, Real.sqrt_le_iff]
    constructor
    · positivity
    · let z : ℝ := Real.sqrt (t * H₁ * H₂ * H₃ / A ^ 5)
      have hz : 0 ≤ z := by dsimp only [z]; positivity
      have hsz : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz
      have hsq : (((N - s : ℕ) : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
        exact hsubsq
      change 10560 * (((N - s : ℕ) : ℝ)) ^ 2 * H₃ ^ 2 *
          Real.sqrt (t * r * s * H₃ / A ^ 5) ≤
        (103 * N * Real.sqrt z * H₃) ^ 2
      calc
        _ ≤ 10560 * (N : ℝ) ^ 2 * H₃ ^ 2 * z := by gcongr
        _ ≤ 10609 * (N : ℝ) ^ 2 * H₃ ^ 2 * z := by
          have hp : 0 ≤ (N : ℝ) ^ 2 * H₃ ^ 2 * z := by positivity
          nlinarith
        _ = 10609 * (N : ℝ) ^ 2 * H₃ ^ 2 * (Real.sqrt z) ^ 2 := by
          rw [hsz]
        _ = (103 * N * Real.sqrt z * H₃) ^ 2 := by ring
  have hthird :
      Real.sqrt (21120 * (((N - s : ℕ) : ℝ)) * H₃ *
          Real.sqrt (H₃ : ℝ) / Real.sqrt (t * r * s / A ^ 5)) / H₃ ≤
        146 * Real.sqrt (N : ℝ) *
          Real.sqrt (1 /
            (Real.sqrt (H₃ : ℝ) * Real.sqrt (t * r * s / A ^ 5))) := by
    rw [div_le_iff₀ hH, Real.sqrt_le_iff]
    constructor
    · positivity
    · have hdenR : 0 < Real.sqrt (t * (r : ℝ) * s / A ^ 5) :=
        Real.sqrt_pos.2 (by positivity)
      let z : ℝ := Real.sqrt (t * r * s / A ^ 5)
      have hz : 0 < z := by simpa only [z] using hsbase
      have hsN := Real.sq_sqrt (Nat.cast_nonneg N)
      have hroot : Real.sqrt
          (1 / (Real.sqrt (H₃ : ℝ) * z)) ^ 2 =
          1 / (Real.sqrt (H₃ : ℝ) * z) := Real.sq_sqrt (by positivity)
      have hrhs :
          (146 * Real.sqrt (N : ℝ) *
            Real.sqrt (1 / (Real.sqrt (H₃ : ℝ) * z)) * H₃) ^ 2 =
          21316 * (N : ℝ) * H₃ * Real.sqrt (H₃ : ℝ) / z := by
        calc
          (146 * Real.sqrt (N : ℝ) *
              Real.sqrt (1 / (Real.sqrt (H₃ : ℝ) * z)) * H₃) ^ 2 =
            21316 * (Real.sqrt (N : ℝ)) ^ 2 *
              (Real.sqrt (1 / (Real.sqrt (H₃ : ℝ) * z))) ^ 2 * H₃ ^ 2 := by ring
          _ = 21316 * (N : ℝ) *
              (1 / (Real.sqrt (H₃ : ℝ) * z)) * H₃ ^ 2 := by
            rw [hsN, hroot]
          _ = 21316 * (N : ℝ) * H₃ * Real.sqrt (H₃ : ℝ) / z := by
            field_simp [hsH.ne', hz.ne']
            nlinarith [hsHsq]
      change 21120 * (((N - s : ℕ) : ℝ)) * H₃ * Real.sqrt (H₃ : ℝ) /
          Real.sqrt (t * r * s / A ^ 5) ≤
        (146 * Real.sqrt (N : ℝ) *
          Real.sqrt (1 / (Real.sqrt (H₃ : ℝ) * z)) * H₃) ^ 2
      rw [show Real.sqrt (t * r * s / A ^ 5) = z by rfl, hrhs]
      have hfac : 0 ≤ (H₃ : ℝ) * Real.sqrt (H₃ : ℝ) / z := by positivity
      have hcoefSub : 21120 * (((N - s : ℕ) : ℝ)) ≤
          21316 * (N : ℝ) := by nlinarith
      calc
        21120 * (((N - s : ℕ) : ℝ)) * (H₃ : ℝ) *
            Real.sqrt (H₃ : ℝ) / z =
            (21120 * (((N - s : ℕ) : ℝ))) *
              ((H₃ : ℝ) * Real.sqrt (H₃ : ℝ) / z) := by ring
        _ ≤ (21316 * (N : ℝ)) *
              ((H₃ : ℝ) * Real.sqrt (H₃ : ℝ) / z) :=
          mul_le_mul_of_nonneg_right hcoefSub hfac
        _ = 21316 * (N : ℝ) * (H₃ : ℝ) * Real.sqrt (H₃ : ℝ) / z := by ring
  linarith

#print axioms logarithmicThirdCorrelationBound_le_homogeneous
#print axioms logarithmicThirdCorrelationBound_le_simple
#print axioms sum_logarithmicThirdCorrelationBound_le
#print axioms norm_logarithmicSecondDifferenceSum_le_A3Bound
#print axioms logarithmicSecondDifferenceA3Bound_le_raw
#print axioms logarithmicSecondDifferenceA3RawBound_le_separated

end

end GafniTao
