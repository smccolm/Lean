import GafniTao.FordEquation61
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ford's equation (6.7)

The source applies finite Holder to equation (6.1).  This file proves the
finite `L^(2s)` inequality with its exact cardinality exponent and specializes
it to Ford's literal interval `N < n <= 2N-1`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The literal `2s`-moment of Ford's inner sums in (6.7). -/
def fordLemma63Moment (M N : ℕ) (u t : ℝ) (s : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖ ^ (2 * s)

/-- Finite Holder in the root form used in (6.7). -/
theorem ford_sum_le_card_rpow_mul_moment_root
    {α : Type*} (A : Finset α) (f : α → ℝ) {r : ℕ}
    (hr : 1 ≤ r) (hf : ∀ a ∈ A, 0 ≤ f a) :
    (∑ a ∈ A, f a) ≤
      (A.card : ℝ) ^ (1 - 1 / (r : ℝ)) *
        (∑ a ∈ A, f a ^ r) ^ (1 / (r : ℝ)) := by
  let X : ℝ := ∑ a ∈ A, f a
  let Y : ℝ := ∑ a ∈ A, f a ^ r
  have hX : 0 ≤ X := Finset.sum_nonneg hf
  have hY : 0 ≤ Y := Finset.sum_nonneg fun a ha => pow_nonneg (hf a ha) r
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hpow : X ^ r ≤ (A.card : ℝ) ^ (r - 1) * Y := by
    dsimp [X, Y]
    have h := pow_sum_le_card_mul_sum_pow hf (r - 1)
    rw [Nat.sub_add_cancel hr] at h
    exact h
  have hroot :
      X ≤ ((A.card : ℝ) ^ (r - 1) * Y) ^ (1 / (r : ℝ)) := by
    rw [show 1 / (r : ℝ) = ((r : ℝ))⁻¹ by ring]
    rw [Real.le_rpow_inv_iff_of_pos hX (mul_nonneg (pow_nonneg (by positivity) _) hY)
      hrpos]
    simpa only [Real.rpow_natCast] using hpow
  calc
    X ≤ ((A.card : ℝ) ^ (r - 1) * Y) ^ (1 / (r : ℝ)) := hroot
    _ = ((A.card : ℝ) ^ (r - 1)) ^ (1 / (r : ℝ)) *
        Y ^ (1 / (r : ℝ)) := by
      rw [Real.mul_rpow (pow_nonneg (by positivity) _) hY]
    _ = (A.card : ℝ) ^ (1 - 1 / (r : ℝ)) *
        Y ^ (1 / (r : ℝ)) := by
      congr 1
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (Nat.cast_nonneg A.card)]
      congr 1
      have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrpos
      have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub hr]
        norm_num
      rw [hcast]
      field_simp [hrne]

/-- Ford's equation (6.7), retaining exactly the `N/M+M` boundary loss and
the `N^(1-1/(2s))` Holder factor. -/
theorem ford_equation_6_7
    {M N R s : ℕ} {u t : ℝ}
    (hM : 1 ≤ M) (hMN : M ≤ N) (hN : 1 ≤ N) (hs : 1 ≤ s)
    (hR : R ≤ 2 * N) (hu : 0 < u) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / M *
          (fordLemma63Moment M N u t s) ^ (1 / (2 * s : ℝ)) +
        (N : ℝ) / M + M := by
  have h61 := ford_equation_6_1
    (M := M) (N := N) (R := R) (u := u) (t := t) hM hMN hR hu
  let A := Finset.Ioc N (2 * N - 1)
  let f : ℕ → ℝ := fun n => ‖fordLemma63T M n u t‖
  have hrs : 1 ≤ 2 * s := by omega
  have hholder := ford_sum_le_card_rpow_mul_moment_root A f hrs
    (fun n hn => norm_nonneg _)
  have hcard : A.card ≤ N := by
    dsimp [A]
    rw [Nat.card_Ioc]
    omega
  have hexp : (0 : ℝ) ≤ 1 - 1 / (2 * s : ℝ) := by
    have hsR : (1 : ℝ) ≤ 2 * s := by exact_mod_cast hrs
    have hpos : (0 : ℝ) < 2 * s := lt_of_lt_of_le zero_lt_one hsR
    have hinv : 1 / (2 * s : ℝ) ≤ 1 := by
      exact (div_le_one hpos).2 hsR
    linarith
  have hcardR : (A.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hcardPow :
      (A.card : ℝ) ^ (1 - 1 / (2 * s : ℝ)) ≤
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcardR hexp
  have hmomentNonneg : 0 ≤ fordLemma63Moment M N u t s := by
    unfold fordLemma63Moment
    positivity
  have hsum :
      (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) ≤
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (fordLemma63Moment M N u t s) ^ (1 / (2 * s : ℝ)) := by
    calc
      _ ≤ (A.card : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (∑ n ∈ A, f n ^ (2 * s)) ^ (1 / (2 * s : ℝ)) := by
        simpa only [A, f, Nat.cast_mul, Nat.cast_ofNat] using hholder
      _ ≤ (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (∑ n ∈ A, f n ^ (2 * s)) ^ (1 / (2 * s : ℝ)) := by
        gcongr
      _ = _ := by rfl
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        (1 / (M : ℝ)) *
            (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T M n u t‖) +
          (N : ℝ) / M + M := h61
    _ ≤ (1 / (M : ℝ)) *
          ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
            (fordLemma63Moment M N u t s) ^ (1 / (2 * s : ℝ))) +
          (N : ℝ) / M + M := by gcongr
    _ = _ := by ring

#print axioms ford_sum_le_card_rpow_mul_moment_root
#print axioms ford_equation_6_7

end

end GafniTao
