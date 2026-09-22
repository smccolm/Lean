import TaoTrudgianYang2025.BourgainDifferenceCounts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Polynomial overlap loss for moving integer windows

The overlap is at most `2 ceil(H) + 1`, independently of the number of
centres. This preserves a small-power window loss when `H = T^ε`.
-/

open Finset MeasureTheory
open scoped Interval

noncomputable section

namespace TaoTrudgianYang2025

/-- Actual integer centres whose radius-`H` intervals contain a fixed point
occupy a single finite integer interval. -/
theorem bourgain_integer_window_count_le
    (D : Finset ℤ) (H x : ℝ) :
    (D.filter fun ℓ : ℤ => x ∈ Set.Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)).card ≤
      2 * Nat.ceil H + 1 := by
  classical
  let K := Nat.ceil H
  have hHK : H ≤ (K : ℝ) := Nat.le_ceil H
  have hsub : (D.filter fun ℓ : ℤ => x ∈ Set.Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)) ⊆
      Finset.Icc (⌊x⌋ - (K : ℤ)) (⌊x⌋ + (K : ℤ)) := by
    intro ℓ hℓ
    obtain ⟨hb₁, hb₂⟩ := (Finset.mem_filter.mp hℓ).2
    apply Finset.mem_Icc.mpr
    constructor
    · have hr : (⌊x⌋ : ℝ) - (K : ℝ) ≤ (ℓ : ℝ) := by
        linarith [Int.floor_le x]
      exact_mod_cast hr
    · have hr : (ℓ : ℝ) < (⌊x⌋ : ℝ) + (K : ℝ) + 1 := by
        linarith [Int.lt_floor_add_one x]
      have hi : ℓ < ⌊x⌋ + (K : ℤ) + 1 := by exact_mod_cast hr
      omega
  have hc := Finset.card_le_card hsub
  have heq : (Finset.Icc (⌊x⌋ - (K : ℤ)) (⌊x⌋ + (K : ℤ))).card = 2*K+1 := by
    rw [Int.card_Icc]
    have hi : ⌊x⌋ + (K : ℤ) + 1 - (⌊x⌋ - (K : ℤ)) = ((2*K+1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hi, Int.toNat_natCast]
  exact heq ▸ hc

/-- Finite translated-window overlap inside an actual integral. All
integrability and set-containment obligations are derived from continuity
and the range of the integer centres. -/
theorem bourgain_sum_integer_window_integral_le
    (D : Finset ℤ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (H a b : ℝ) (hH : 0 ≤ H) (hab : a ≤ b)
    (hrange : ∀ ℓ ∈ D, a ≤ (ℓ : ℝ) ∧ (ℓ : ℝ) ≤ b) :
    (∑ ℓ ∈ D, ∫ x in (ℓ : ℝ)-H..(ℓ : ℝ)+H, f x) ≤
      (2 * Nat.ceil H + 1 : ℕ) * ∫ x in a-H..b+H, f x := by
  classical
  let J := Set.Ioc (a-H) (b+H)
  let window := fun ℓ : ℤ => Set.Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)
  have hfi (c d : ℝ) : IntegrableOn f (Set.Ioc c d) :=
    hf.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hwi (ℓ : ℤ) : Integrable ((window ℓ).indicator f) :=
    (hfi _ _).integrable_indicator measurableSet_Ioc
  have hJi : Integrable (J.indicator f) :=
    (hfi _ _).integrable_indicator measurableSet_Ioc
  have hsub (ℓ : ℤ) (hℓ : ℓ ∈ D) : window ℓ ⊆ J := by
    intro x hx
    have hr := hrange ℓ hℓ
    change (ℓ : ℝ)-H < x ∧ x ≤ (ℓ : ℝ)+H at hx
    constructor <;> linarith [hx.1, hx.2]
  have hpoint (x : ℝ) :
      (∑ ℓ ∈ D, (window ℓ).indicator f x) ≤
        (2 * Nat.ceil H + 1 : ℕ) * J.indicator f x := by
    by_cases hx : x ∈ J
    · rw [Set.indicator_of_mem hx]
      have heq : (∑ ℓ ∈ D, (window ℓ).indicator f x) =
          ((D.filter fun ℓ => x ∈ window ℓ).card : ℝ) * f x := by
        calc
          _ = ∑ ℓ ∈ D.filter (fun ℓ => x ∈ window ℓ), f x := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            by_cases hw : x ∈ window ℓ <;> simp [hw]
          _ = _ := by simp
      rw [heq]
      apply mul_le_mul_of_nonneg_right _ (hf0 x)
      exact_mod_cast bourgain_integer_window_count_le D H x
    · rw [Set.indicator_of_notMem hx]
      have hz : ∀ ℓ ∈ D, (window ℓ).indicator f x = 0 := by
        intro ℓ hℓ
        apply Set.indicator_of_notMem
        intro hw
        exact hx (hsub ℓ hℓ hw)
      simp only [Finset.sum_eq_zero hz, mul_zero, le_refl]
  have hleft :
      (∑ ℓ ∈ D, ∫ x in (ℓ : ℝ)-H..(ℓ : ℝ)+H, f x) =
        ∫ x, ∑ ℓ ∈ D, (window ℓ).indicator f x := by
    rw [MeasureTheory.integral_finsetSum D (fun ℓ _ => hwi ℓ)]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [hleft]
  calc
    _ ≤ ∫ x, (2 * Nat.ceil H + 1 : ℕ) * J.indicator f x :=
      MeasureTheory.integral_mono
        (integrable_finsetSum D (fun ℓ _ => hwi ℓ)) (hJi.const_mul _) hpoint
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_indicator measurableSet_Ioc,
        intervalIntegral.integral_of_le (by linarith)]

/-- Moving each actual real difference to its floor costs a unit enlargement
of the window. This is the explicit endpoint-safe form of Bourgain (4.19);
a same-radius replacement is not asserted. -/
theorem bourgain_difference_window_integral_le
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (H : ℝ) (hH : 0 ≤ H) :
    (∑ p ∈ W ×ˢ W, ∫ u in -H..H, f (p.1-p.2+u)) ≤
      ∑ ℓ ∈ bourgainDifferenceSupport W, (bourgainDifferenceCount W ℓ : ℝ) *
        ∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u) := by
  classical
  rw [bourgainDifferenceCount_weighted_eq]
  apply Finset.sum_le_sum
  intro p hp
  let ℓ : ℤ := ⌊p.1-p.2⌋
  have hfloor : (ℓ : ℝ) ≤ p.1-p.2 := Int.floor_le _
  have hceil : p.1-p.2 < (ℓ : ℝ)+1 := Int.lt_floor_add_one _
  have hnear : |p.1-p.2-(ℓ : ℝ)| < 1 := abs_lt.mpr (by constructor <;> linarith)
  have hℓ : ℓ ∈ bourgainDifferenceSupport W :=
    Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_insert_self _ _⟩
  have hleft :
      (∫ u in -H..H, f (p.1-p.2+u)) = ∫ x in p.1-p.2-H..p.1-p.2+H, f x := by
    convert intervalIntegral.integral_comp_add_left f (p.1-p.2) using 1
  have hright :
      (∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u)) =
        ∫ x in (ℓ : ℝ)-(H+1)..(ℓ : ℝ)+(H+1), f x := by
    convert intervalIntegral.integral_comp_add_left f (ℓ : ℝ) using 1
  have hmove :
      (∫ u in -H..H, f (p.1-p.2+u)) ≤
        ∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u) := by
    rw [hleft, hright]
    apply intervalIntegral.integral_mono_interval
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall hf0
    · exact hf.intervalIntegrable _ _
  have hnn (k : ℤ) (_hk : k ∈ bourgainDifferenceSupport W) :
      0 ≤ if |p.1-p.2-(k : ℝ)| < 1 then
        ∫ u in -(H+1)..H+1, f ((k : ℝ)+u) else 0 := by
    split_ifs
    · exact intervalIntegral.integral_nonneg (by linarith) (fun _ _ => hf0 _)
    · exact le_rfl
  calc
    _ ≤ ∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u) := hmove
    _ = if |p.1-p.2-(ℓ : ℝ)| < 1 then
        ∫ u in -(H+1)..H+1, f ((ℓ : ℝ)+u) else 0 := (if_pos hnear).symm
    _ ≤ _ := Finset.single_le_sum hnn hℓ

end TaoTrudgianYang2025
