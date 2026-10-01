import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace HuxleyColorWeightAbsorptionScratch

private theorem actual_color_tenth_weight_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) :
    (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ)^10) ≤
      (V.card:ℝ)^10 := by
  have hcard :
      (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ))=(V.card:ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_image color V).symm
  calc
    _ = ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*
          ((V.filter (fun i => color i=key)).card:ℝ)^9 := by
      apply Finset.sum_congr rfl
      intro key _
      rw [pow_succ']
    _ ≤ ∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)*(V.card:ℝ)^9 := by
      apply Finset.sum_le_sum
      intro key _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_filter_le V (fun i => color i=key)
    _ = (V.card:ℝ)^10 := by
      rw [←Finset.sum_mul,hcard]
      ring

private theorem actual_color_tenth_weight_absorption
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) {X C B : ℝ}
    (hX : 0 ≤ X)
    (hbound : X ≤ C*(∑ key∈V.image color,
      ((V.filter (fun i => color i=key)).card:ℝ)^10*B)) :
    X ≤ C*(V.card:ℝ)^10*B := by
  classical
  by_cases hV : V=∅
  · simpa only [hV,Finset.image_empty,Finset.sum_empty,Finset.card_empty,Nat.cast_zero,
      zero_pow (by decide : (10:ℕ)≠0),mul_zero,zero_mul] using hbound
  · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hV
    have hf : 0 < (V.filter (fun j => color j=color i)).card :=
      Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩
    have hweight : 0 < ∑ key∈V.image color,
        ((V.filter (fun j => color j=key)).card:ℝ)^10 :=
      lt_of_lt_of_le (pow_pos (Nat.cast_pos.mpr hf) 10)
        (Finset.single_le_sum
          (f:=fun key => ((V.filter (fun j => color j=key)).card:ℝ)^10)
          (fun key _ => pow_nonneg (Nat.cast_nonneg _) 10)
          (Finset.mem_image_of_mem color hi))
    have hbound' : X ≤ (C*B)*(∑ key∈V.image color,
        ((V.filter (fun i => color i=key)).card:ℝ)^10) := by
      calc
        X ≤ _ := hbound
        _ = _ := by rw [←Finset.sum_mul]; ac_rfl
    have hCB : 0 ≤ C*B := nonneg_of_mul_nonneg_left (hX.trans hbound') hweight
    calc
      X ≤ _ := hbound'
      _ ≤ (C*B)*(V.card:ℝ)^10 :=
        mul_le_mul_of_nonneg_left (actual_color_tenth_weight_bound V color) hCB
      _ = _ := by ac_rfl

example
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) :
    (∑ key∈V.image color, ((V.filter (fun i => color i=key)).card:ℝ)^10) ≤
      (V.card:ℝ)^10 :=
  HuxleyColorWeightAbsorptionScratch.actual_color_tenth_weight_bound (α:=α) (β:=β) V color

example
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (color : α → β) {X C B : ℝ}
    (hX : 0 ≤ X)
    (hbound : X ≤ C*(∑ key∈V.image color,
      ((V.filter (fun i => color i=key)).card:ℝ)^10*B)) :
    X ≤ C*(V.card:ℝ)^10*B :=
  HuxleyColorWeightAbsorptionScratch.actual_color_tenth_weight_absorption (α:=α) (β:=β) V color (X:=X) (C:=C) (B:=B) hX hbound

#print axioms actual_color_tenth_weight_bound
#print axioms actual_color_tenth_weight_absorption
end HuxleyColorWeightAbsorptionScratch
