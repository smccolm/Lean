import GafniTao.FordLemma51Equation53
import Mathlib.Data.Int.Interval

/-!
# Integer points in a real interval

This is the floor/ceiling counting lemma used in Ford's spacing estimate
(5.6).  Both endpoints remain real, so no endpoint loss is hidden in an
integer replacement.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The exact finite set of integer points in the open real interval
`(a,b)`. -/
def fordIntegerOpenInterval (a b : ℝ) : Finset ℤ :=
  (Finset.Icc ⌈a⌉ ⌊b⌋).filter fun n => a < (n : ℝ) ∧ (n : ℝ) < b

theorem mem_fordIntegerOpenInterval {a b : ℝ} {n : ℤ} :
    n ∈ fordIntegerOpenInterval a b ↔ a < (n : ℝ) ∧ (n : ℝ) < b := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr hn.1.le, Int.le_floor.mpr hn.2.le⟩, hn⟩

theorem card_int_Icc_ceil_floor_cast_le {a b : ℝ} (hab : a ≤ b) :
    ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) ≤ b - a + 1 := by
  by_cases h : ⌈a⌉ ≤ ⌊b⌋ + 1
  · have hcard : ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℤ) =
        ⌊b⌋ + 1 - ⌈a⌉ := Int.card_Icc_of_le
          (a := ⌈a⌉) (b := ⌊b⌋) h
    calc
      ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) =
          ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by exact_mod_cast hcard
      _ ≤ b - a + 1 := by
        have hfloor : ((⌊b⌋ : ℤ) : ℝ) ≤ b := Int.floor_le b
        have hceil : a ≤ ((⌈a⌉ : ℤ) : ℝ) := Int.le_ceil a
        push_cast
        linarith
  · have hlt : ⌊b⌋ < ⌈a⌉ := by omega
    have hempty : Finset.Icc ⌈a⌉ ⌊b⌋ = ∅ := by
      exact Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp
    linarith

/-- An open interval of length `b-a` contains at most `b-a+1` integers. -/
theorem fordIntegerOpenInterval_card_cast_le {a b : ℝ} (hab : a ≤ b) :
    ((fordIntegerOpenInterval a b).card : ℝ) ≤ b - a + 1 := by
  have hcard := Finset.card_filter_le
    (s := Finset.Icc ⌈a⌉ ⌊b⌋)
    (p := fun n : ℤ => a < (n : ℝ) ∧ (n : ℝ) < b)
  have hcardReal : ((fordIntegerOpenInterval a b).card : ℝ) ≤
      ((Finset.Icc ⌈a⌉ ⌊b⌋).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans (card_int_Icc_ceil_floor_cast_le hab)

#print axioms mem_fordIntegerOpenInterval
#print axioms fordIntegerOpenInterval_card_cast_le

end

end GafniTao
