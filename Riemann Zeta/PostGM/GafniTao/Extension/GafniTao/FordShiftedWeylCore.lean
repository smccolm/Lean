import GafniTao.FordLambdaScale
import RiemannZeta.GuthMaynard.WeylExplicit

/-!
# A shifted real-base Weyl estimate

Ford's short logarithmic sum starts at the real point `N + 1 + u`, not at
an integer.  The frozen Weyl module already proves the A- and B-processes
for a real base; only its final convenience theorem specializes the base to
an integer.  This file carries out that final optimization for a real base
and an arbitrary terminal prefix.  Consequently no displacement of `u` and
no unproved uniformity convention is hidden in the application.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The classical A-process shift length for a positive real base. -/
def fordRealWeylShiftLength (Y A : ℝ) : ℕ := Nat.floor (A / Y)

theorem fordRealWeylShiftLength_spec
    {Y A : ℝ} (hY : 1 ≤ Y) (hA : 0 < A) (hYA : Y ≤ A) :
    let H := fordRealWeylShiftLength Y A
    0 < H ∧ (H : ℝ) * Y ≤ A ∧ A ≤ 2 * H * Y := by
  dsimp only [fordRealWeylShiftLength]
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hxOne : (1 : ℝ) ≤ A / Y := by
    rw [le_div_iff₀ hYpos]
    simpa only [one_mul] using hYA
  have hpos : 0 < Nat.floor (A / Y) := Nat.floor_pos.mpr hxOne
  have hfloor : ((Nat.floor (A / Y) : ℕ) : ℝ) ≤ A / Y :=
    Nat.floor_le (by positivity)
  have hHY : ((Nat.floor (A / Y) : ℕ) : ℝ) * Y ≤ A := by
    calc
      ((Nat.floor (A / Y) : ℕ) : ℝ) * Y ≤ (A / Y) * Y :=
        mul_le_mul_of_nonneg_right hfloor hYpos.le
      _ = A := by field_simp
  have hxLt : A / Y < ((Nat.floor (A / Y) + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (A / Y)
  have hfloorOne : (1 : ℝ) ≤ ((Nat.floor (A / Y) : ℕ) : ℝ) := by
    exact_mod_cast hpos
  have hxTwo : A / Y ≤ 2 * ((Nat.floor (A / Y) : ℕ) : ℝ) := by
    push_cast at hxLt
    linarith
  have hAH : A ≤ 2 * ((Nat.floor (A / Y) : ℕ) : ℝ) * Y := by
    rw [← div_le_iff₀ hYpos]
    exact hxTwo
  exact ⟨hpos, hHY, hAH⟩

/-- The uniform correlation estimate from the frozen B-process, now with a
real base and an independently truncated prefix length. -/
theorem ford_simpleLogarithmicCorrelationBound_le
    {Y X A : ℝ} {L H : ℕ}
    (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hLA : (L : ℝ) ≤ A) (hHY : (H : ℝ) * Y ≤ A)
    (hAY : A ^ 2 ≤ X * Y ^ 3) :
    simpleLogarithmicCorrelationBound (Y ^ 3) A L H ≤ 400 * X * Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  let q : ℝ := Y ^ 3 / (8 * A ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqH_le : q * H ≤ (Y / A) ^ 2 := by
    dsimp only [q]
    rw [show Y ^ 3 / (8 * A ^ 3) * (H : ℝ) =
      (Y ^ 3 * H) / (8 * A ^ 3) by ring]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * A ^ 3)
      (by positivity : 0 < A ^ 2)]
    calc
      Y ^ 3 * (H : ℝ) * A ^ 2 =
          ((H : ℝ) * Y) * (Y ^ 2 * A ^ 2) := by ring
      _ ≤ A * (Y ^ 2 * A ^ 2) :=
        mul_le_mul_of_nonneg_right hHY
          (mul_nonneg (pow_nonneg hYpos.le 2) (pow_nonneg hA.le 2))
      _ ≤ 8 * A * (Y ^ 2 * A ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = Y ^ 2 * (8 * A ^ 3) := by ring
  have hsqrtHigh : Real.sqrt (q * H) ≤ Y / A := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hqH_le⟩
  have hfirst : (L : ℝ) * Real.sqrt (q * H) ≤ Y := by
    calc
      (L : ℝ) * Real.sqrt (q * H) ≤ A * Real.sqrt (q * H) :=
        mul_le_mul_of_nonneg_right hLA (Real.sqrt_nonneg _)
      _ ≤ A * (Y / A) := mul_le_mul_of_nonneg_left hsqrtHigh hA.le
      _ = Y := by field_simp
  have hY3_le_Y4 : Y ^ 3 ≤ Y ^ 4 := by
    have := mul_le_mul_of_nonneg_left hY (pow_nonneg hYpos.le 3)
    nlinarith
  have hX_le_X2 : X ≤ X ^ 2 := by nlinarith
  have hA_le_XY2 : A ≤ X * Y ^ 2 := by
    have hsquares : A ^ 2 ≤ (X * Y ^ 2) ^ 2 := by
      calc
        A ^ 2 ≤ X * Y ^ 3 := hAY
        _ ≤ X * Y ^ 4 := mul_le_mul_of_nonneg_left hY3_le_Y4 hXpos.le
        _ ≤ X ^ 2 * Y ^ 4 :=
          mul_le_mul_of_nonneg_right hX_le_X2 (pow_nonneg hYpos.le 4)
        _ = (X * Y ^ 2) ^ 2 := by ring
    nlinarith [sq_nonneg (A - X * Y ^ 2)]
  have hA3_le : A ^ 3 ≤ X ^ 2 * Y ^ 5 := by
    calc
      A ^ 3 = A ^ 2 * A := by ring
      _ ≤ (X * Y ^ 3) * (X * Y ^ 2) :=
        mul_le_mul hAY hA_le_XY2 hA.le
          (mul_nonneg hXpos.le (pow_nonneg hYpos.le 3))
      _ = X ^ 2 * Y ^ 5 := by ring
  have hsquareLow : (1 / (3 * X * Y)) ^ 2 ≤ q := by
    dsimp only [q]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < (3 * X * Y) ^ 2)
      (by positivity : 0 < 8 * A ^ 3)]
    nlinarith [hA3_le,
      mul_nonneg (pow_nonneg hXpos.le 2) (pow_nonneg hYpos.le 5)]
  have hsqrtLow : 1 / (3 * X * Y) ≤ Real.sqrt q :=
    Real.le_sqrt_of_sq_le hsquareLow
  have hsecond : 1 / Real.sqrt q ≤ 3 * X * Y := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hq)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtLow
      (by positivity : 0 ≤ 3 * X * Y)
    field_simp [hXpos.ne', hYpos.ne'] at hmul
    nlinarith
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  change 100 * ((L : ℝ) * Real.sqrt (q * H) + 1 / Real.sqrt q) ≤
    400 * X * Y
  nlinarith [mul_pos hXpos hYpos]

theorem ford_norm_integerLogarithmicPrefix_le_length
    (t A : ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) L, integerLogarithmicTerm t A n‖ ≤ L := by
  calc
    ‖∑ n ∈ Finset.Ico (0 : ℤ) L, integerLogarithmicTerm t A n‖ ≤
        ∑ n ∈ Finset.Ico (0 : ℤ) L, ‖integerLogarithmicTerm t A n‖ :=
      norm_sum_le _ _
    _ = L := by simp [Int.card_Ico]

/-- Real-base, arbitrary-prefix `(1/6,2/3)` estimate. -/
theorem ford_real_base_weyl_prefix
    {Y X A : ℝ} {L : ℕ}
    (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hYA : Y ≤ A) (hAY : A ^ 2 ≤ X * Y ^ 3)
    (hLA : (L : ℝ) ≤ A) :
    ‖∑ n ∈ Finset.Ico (0 : ℤ) L,
        integerLogarithmicTerm (Y ^ 3) A n‖ ≤
      30 * Real.sqrt (X * A * Y) := by
  let H := fordRealWeylShiftLength Y A
  obtain ⟨hH, hHY, hAH⟩ := fordRealWeylShiftLength_spec hY hA hYA
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hHreal : 0 < (H : ℝ) := Nat.cast_pos.mpr hH
  have hsqrtSq : Real.sqrt (X * A * Y) ^ 2 = X * A * Y :=
    Real.sq_sqrt (by positivity)
  have hsqrtNonneg : 0 ≤ Real.sqrt (X * A * Y) := Real.sqrt_nonneg _
  by_cases hHL : H ≤ L
  · have hsmall : Y ^ 3 * (H : ℝ) / (8 * A ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 8 * A ^ 3)]
      calc
        Y ^ 3 * (H : ℝ) = ((H : ℝ) * Y) * Y ^ 2 := by ring
        _ ≤ A * Y ^ 2 :=
          mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
        _ ≤ A * A ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith
          · exact hA.le
        _ ≤ 8 * A ^ 3 := by nlinarith [pow_pos hA 3]
    have hab := logarithmic_weyl_AB_process_simple
      (Y ^ 3) A L H (pow_pos hYpos 3) hA hHL hLA hsmall
    have hc := ford_simpleLogarithmicCorrelationBound_le
      hY hX hA hLA hHY hAY
    have hab' :
        (H : ℝ) ^ 2 *
            ‖∑ n ∈ Finset.Ico (0 : ℤ) L,
              integerLogarithmicTerm (Y ^ 3) A n‖ ^ 2 ≤
          (((L + H : ℕ) : ℝ) *
            ((H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y))) := by
      exact hab.trans (by gcongr)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
    have hHleA : (H : ℝ) ≤ A := by
      calc
        (H : ℝ) = (H : ℝ) * 1 := by ring
        _ ≤ (H : ℝ) * Y :=
          mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg H)
        _ ≤ A := hHY
    have houter : (L : ℝ) + H ≤ 2 * A := by nlinarith
    have hinner : (H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y) ≤
        402 * X * (H : ℝ) ^ 2 * Y := by
      have hHLterm : (H : ℝ) * L ≤ 2 * (H : ℝ) ^ 2 * Y := by
        have hLAH := hLA.trans hAH
        have := mul_le_mul_of_nonneg_left hLAH (Nat.cast_nonneg H)
        nlinarith
      have hFirst : 2 * (H : ℝ) ^ 2 * Y ≤
          2 * X * (H : ℝ) ^ 2 * Y := by
        have hNonneg : 0 ≤ 2 * (H : ℝ) ^ 2 * Y := by positivity
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg (H : ℝ)) hYpos.le]
    have hrightNonneg : 0 ≤
        (H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y) := by positivity
    have hbound :
        (((L : ℝ) + H) *
            ((H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y))) ≤
          900 * (H : ℝ) ^ 2 * X * A * Y := by
      calc
        ((L : ℝ) + H) *
            ((H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y)) ≤
            (2 * A) *
              ((H : ℝ) * L + (H : ℝ) ^ 2 * (400 * X * Y)) :=
          mul_le_mul_of_nonneg_right houter hrightNonneg
        _ ≤ (2 * A) * (402 * X * (H : ℝ) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ 900 * (H : ℝ) ^ 2 * X * A * Y := by
          have hnonneg := mul_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg (H : ℝ)) hXpos.le) hA.le)
            hYpos.le
          nlinarith
    have hsq :
        ‖∑ n ∈ Finset.Ico (0 : ℤ) L,
          integerLogarithmicTerm (Y ^ 3) A n‖ ^ 2 ≤ 900 * X * A * Y := by
      have := hab'.trans hbound
      nlinarith [sq_pos_of_pos hHreal]
    nlinarith [hsqrtNonneg, norm_nonneg (∑ n ∈ Finset.Ico (0 : ℤ) L,
      integerLogarithmicTerm (Y ^ 3) A n)]
  · have hLH : L < H := Nat.lt_of_not_ge hHL
    have htrivial := ford_norm_integerLogarithmicPrefix_le_length (Y ^ 3) A L
    have hHsq : (H : ℝ) ^ 2 ≤ X * A * Y := by
      have hHYsq : ((H : ℝ) * Y) ^ 2 ≤ A ^ 2 := by
        nlinarith [sq_nonneg (A - (H : ℝ) * Y)]
      have hmul : Y ^ 2 * (H : ℝ) ^ 2 ≤ X * Y ^ 3 := by
        calc
          Y ^ 2 * (H : ℝ) ^ 2 = ((H : ℝ) * Y) ^ 2 := by ring
          _ ≤ A ^ 2 := hHYsq
          _ ≤ X * Y ^ 3 := hAY
      have hHYroot : (H : ℝ) ^ 2 ≤ X * Y := by
        by_contra hnot
        have hlt : X * Y < (H : ℝ) ^ 2 := lt_of_not_ge hnot
        have hcontra : X * Y ^ 3 < Y ^ 2 * (H : ℝ) ^ 2 := by
          calc
            X * Y ^ 3 = Y ^ 2 * (X * Y) := by ring
            _ < Y ^ 2 * (H : ℝ) ^ 2 :=
              mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hYpos)
        exact (not_lt_of_ge hmul) hcontra
      have hAone : (1 : ℝ) ≤ A := hY.trans hYA
      have hXA : X * Y ≤ X * A * Y := by
        have hXY : 0 ≤ X * Y := by positivity
        nlinarith
      exact hHYroot.trans hXA
    have hLlt : (L : ℝ) < H := by exact_mod_cast hLH
    have hnorm :
        ‖∑ n ∈ Finset.Ico (0 : ℤ) L,
          integerLogarithmicTerm (Y ^ 3) A n‖ ≤ H := htrivial.trans hLlt.le
    have hnormSq :
        ‖∑ n ∈ Finset.Ico (0 : ℤ) L,
          integerLogarithmicTerm (Y ^ 3) A n‖ ^ 2 ≤ X * A * Y := by
      nlinarith [norm_nonneg (∑ n ∈ Finset.Ico (0 : ℤ) L,
        integerLogarithmicTerm (Y ^ 3) A n)]
    nlinarith [hsqrtNonneg, norm_nonneg (∑ n ∈ Finset.Ico (0 : ℤ) L,
      integerLogarithmicTerm (Y ^ 3) A n)]

#print axioms fordRealWeylShiftLength_spec
#print axioms ford_simpleLogarithmicCorrelationBound_le
#print axioms ford_real_base_weyl_prefix

end

end GafniTao
