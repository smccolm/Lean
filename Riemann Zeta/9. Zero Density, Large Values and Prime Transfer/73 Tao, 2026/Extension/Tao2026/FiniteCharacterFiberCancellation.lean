import Tao2026.BurgessWeilPrimeKummerWeilAmplification

/-!
# Character cancellation from one-sided fiber bounds

Subtracting a common fiber upper bound leaves nonnegative deficits. The zero
sum of a nontrivial character then bounds its weighted sum by the total deficit.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem finite_complex_sum_norm_le_of_fiber_card_upper
    {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (w : B → ℂ) (S : Finset B) (U : ℝ)
    (hzero : ∀ b ∉ S, w b = 0) (hsum : ∑ b ∈ S, w b = 0)
    (hnorm : ∀ b ∈ S, ‖w b‖ ≤ 1)
    (hcard : ∀ b ∈ S, ((univ.filter fun a => f a = b).card : ℝ) ≤ U) :
    ‖∑ a, w (f a)‖ ≤ S.card * U - ((univ.filter fun a => f a ∈ S).card : ℝ) := by
  classical
  have hgroup : (∑ b ∈ S, ((univ.filter fun a => f a = b).card : ℂ) * w b) = ∑ a, w (f a) := by
    calc
      _ = ∑ b ∈ S, ∑ _a ∈ univ.filter (fun a => f a = b), w b := by simp
      _ = ∑ a ∈ univ.filter (fun a => f a ∈ S), w (f a) :=
        Finset.sum_fiberwise_eq_sum_filter' univ S f w
      _ = _ := by
        apply Finset.sum_subset (filter_subset _ _)
        intro a _ ha
        exact hzero (f a) (by simpa using ha)
  have hshift : (∑ b ∈ S, (((univ.filter fun a => f a = b).card : ℂ) - U) * w b) =
      ∑ a, w (f a) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
    exact hgroup
  rw [← hshift]
  calc
    _ ≤ ∑ b ∈ S, ‖(((univ.filter fun a => f a = b).card : ℂ) - U) * w b‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ S, (U - ((univ.filter fun a => f a = b).card : ℝ)) := by
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul, show (((univ.filter fun a => f a = b).card : ℂ) - U) =
        ((((univ.filter fun a => f a = b).card : ℝ) - U : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.2 (hcard b hb))]
      nlinarith [hnorm b hb, hcard b hb]
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [sum_const, nsmul_eq_mul]
      congr 1
      rw [← Nat.cast_sum, Finset.sum_card_fiberwise_eq_card_filter]

theorem prime_mulChar_sum_norm_le_of_fiber_card_upper
    {A : Type*} [Fintype A] (p : ℕ) [NeZero p] [Fact p.Prime]
    (f : A → ZMod p) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (U : ℝ)
    (hcard : ∀ b : ZMod p, b ≠ 0 → ((univ.filter fun a => f a = b).card : ℝ) ≤ U) :
    ‖∑ a, χ (f a)‖ ≤ (p - 1 : ℕ) * U - Fintype.card A +
      ((univ.filter fun a => f a = 0).card : ℝ) := by
  classical
  have hsum : (∑ b ∈ (univ : Finset (ZMod p)).erase 0, χ b) = 0 := by
    rw [sum_erase_eq_sub (mem_univ _), MulChar.sum_eq_zero_of_ne_one hχ, MulChar.map_zero, sub_zero]
  have hbound := finite_complex_sum_norm_le_of_fiber_card_upper f χ (univ.erase 0) U
    (fun b hb => by
      have hb0 : b = 0 := by simpa using hb
      simp [hb0, MulChar.map_zero]) hsum
    (fun b _ => DirichletCharacter.norm_le_one χ b)
    (fun b hb => hcard b (Finset.ne_of_mem_erase hb))
  have hpartition := Finset.card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => f a = 0)
  have hpartition' : ((univ.filter fun a => f a = 0).card : ℝ) +
      ((univ.filter fun a => f a ≠ 0).card : ℝ) = Fintype.card A := by exact_mod_cast hpartition
  simp only [Finset.card_erase_of_mem (mem_univ (0 : ZMod p)), card_univ, ZMod.card,
    mem_erase, mem_univ, and_true] at hbound
  linarith

end
end Tao2026
