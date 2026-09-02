import GafniTao.FordLemma36Equation319
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Ford Lemma 3.6: exponential decay consequences -/

namespace GafniTao

noncomputable section

theorem fordPotentialLoss36_lower {k : ℕ} (hk : 1000 ≤ k) :
    2 / (k : ℝ) ≤ fordPotentialLoss36 k := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  unfold fordPotentialLoss36 fordBeta36
  field_simp
  nlinarith [sq_nonneg (42 * (k : ℝ) - 32)]

theorem fordDSequence36_exp_contraction
    {k n : ℕ} (hk : 1000 ≤ k)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k n ≤ fordDSequence36 k 0 *
      Real.exp (-(fordAlpha36 k) * (n : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m := by
        intro m hm
        exact habove m (by omega)
      have hih := ih habovePrev
      have hcontract := fordDSequence36_contraction hk
        (n := n) (fun m hm => habove m (by omega))
      have halpha := fordAlpha36_bounds hk
      have hqexp : 1 - fordAlpha36 k ≤ Real.exp (-fordAlpha36 k) := by
        simpa [add_comm] using Real.add_one_le_exp (-fordAlpha36 k)
      have hd0 : 0 ≤ fordDSequence36 k 0 := by
        exact (fordDSequence36_bounds_of_above hk
          (n := 0) (fun _ h => by omega)).1.le
      calc
        fordDSequence36 k (n + 1) ≤
            fordDSequence36 k n * (1 - fordAlpha36 k) := hcontract
        _ ≤ (fordDSequence36 k 0 *
              Real.exp (-(fordAlpha36 k) * (n : ℝ))) *
            (1 - fordAlpha36 k) := by
              exact mul_le_mul_of_nonneg_right hih (sub_nonneg.mpr halpha.2.le)
        _ ≤ (fordDSequence36 k 0 *
              Real.exp (-(fordAlpha36 k) * (n : ℝ))) *
            Real.exp (-fordAlpha36 k) := by
              exact mul_le_mul_of_nonneg_left hqexp (mul_nonneg hd0 (Real.exp_pos _).le)
        _ = fordDSequence36 k 0 *
            Real.exp (-(fordAlpha36 k) * ((n + 1 : ℕ) : ℝ)) := by
              rw [mul_assoc, ← Real.exp_add]
              push_cast
              congr 2
              ring

theorem fordAlpha36_two_k_lower {k : ℕ} (hk : 1000 ≤ k) :
    17 / 5 ≤ fordAlpha36 k * (2 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  unfold fordAlpha36 fordBeta36 fordC36
  field_simp
  nlinarith

theorem fordAlpha36_two_k_sub_one_lower {k : ℕ} (hk : 1000 ≤ k) :
    17 / 5 ≤ fordAlpha36 k * (2 * (k : ℝ) - 1) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by positivity
  unfold fordAlpha36 fordBeta36 fordC36
  field_simp
  nlinarith

theorem exp_seventeen_fifths_gt_twenty_five :
    (25 : ℝ) < Real.exp (17 / 5) := by
  have he := Real.exp_one_gt_d9
  have he' : (27182818283 / 10000000000 : ℝ) < Real.exp 1 := by
    norm_num at he ⊢
    exact he
  have htwoFifths := Real.add_one_le_exp (2 / 5 : ℝ)
  have htwoFifths' : (1 : ℝ) + 2 / 5 ≤ Real.exp (2 / 5) := by
    simpa [add_comm] using htwoFifths
  have hprod :
      (27182818283 / 10000000000 : ℝ) ^ 3 * (1 + 2 / 5) <
        Real.exp 1 ^ 3 * Real.exp (2 / 5) := by
    have hp : (27182818283 / 10000000000 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by
      exact pow_lt_pow_left₀ (n := 3) he' (by norm_num) (by norm_num)
    exact mul_lt_mul hp htwoFifths' (by norm_num) (by positivity)
  have hnum : (25 : ℝ) <
      (27182818283 / 10000000000 : ℝ) ^ 3 * (1 + 2 / 5) := by
    norm_num
  calc
    (25 : ℝ) <
        (27182818283 / 10000000000 : ℝ) ^ 3 * (1 + 2 / 5) := hnum
    _ < Real.exp 1 ^ 3 * Real.exp (2 / 5) := hprod
    _ = Real.exp (17 / 5) := by
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      norm_num

theorem fordDSequence36_small_after_two_k
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 2 * k - 1 ≤ n)
    (habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k n < 1 / 50 := by
  have hdecay := fordDSequence36_exp_contraction hk habove
  have halpha := fordAlpha36_bounds hk
  have hnR : 2 * (k : ℝ) - 1 ≤ n := by
    have hkOne : 1 ≤ 2 * k := by omega
    have hcast : (((2 * k - 1 : ℕ) : ℝ)) = 2 * (k : ℝ) - 1 := by
      rw [Nat.cast_sub hkOne]
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast hn
  have hexponent : 17 / 5 ≤ fordAlpha36 k * (n : ℝ) := by
    exact (fordAlpha36_two_k_sub_one_lower hk).trans
      (mul_le_mul_of_nonneg_left hnR halpha.1.le)
  have hexpMono : Real.exp (-(fordAlpha36 k) * (n : ℝ)) ≤
      Real.exp (-(17 / 5 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hinit : fordDSequence36 k 0 < 1 / 2 := by
    rw [fordDSequence36_zero]
    have hk0 : (0 : ℝ) < k := by positivity
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * k)]
    nlinarith
  have hinit0 : 0 < fordDSequence36 k 0 :=
    (fordDSequence36_bounds_of_above hk (n := 0) (fun _ h => by omega)).1
  have hneg : Real.exp (-(17 / 5 : ℝ)) < 1 / 25 := by
    rw [Real.exp_neg]
    rw [one_div]
    exact (inv_lt_inv₀ (Real.exp_pos _) (by norm_num)).2
      exp_seventeen_fifths_gt_twenty_five
  calc
    fordDSequence36 k n ≤ fordDSequence36 k 0 *
        Real.exp (-(fordAlpha36 k) * (n : ℝ)) := hdecay
    _ ≤ fordDSequence36 k 0 * Real.exp (-(17 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hexpMono hinit0.le
    _ < (1 / 2 : ℝ) * Real.exp (-(17 / 5 : ℝ)) :=
      mul_lt_mul_of_pos_right hinit (Real.exp_pos _)
    _ < (1 / 2 : ℝ) * (1 / 25) :=
      mul_lt_mul_of_pos_left hneg (by norm_num)
    _ = 1 / 50 := by norm_num

#print axioms fordPotentialLoss36_lower
#print axioms fordDSequence36_exp_contraction
#print axioms fordAlpha36_two_k_lower
#print axioms fordAlpha36_two_k_sub_one_lower
#print axioms exp_seventeen_fifths_gt_twenty_five
#print axioms fordDSequence36_small_after_two_k

end

end GafniTao
