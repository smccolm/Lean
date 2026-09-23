import TaoTrudgianYang2025.SargosQuarticMomentTransfer

/-! Finite closed-interval grids with explicit endpoint coverage and counts. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

def sargosIntervalGridCount (L h : ℝ) : ℕ := ⌈L/h⌉₊+1

theorem sargosIntervalGridCount_le {L h : ℝ} (hL : 0 ≤ L) (hh : 0 < h) :
    (sargosIntervalGridCount L h : ℝ) ≤ L/h+2 := by
  have hc := Nat.ceil_lt_add_one (div_nonneg hL hh.le)
  unfold sargosIntervalGridCount
  push_cast
  linarith only [hc]

theorem sargosIntervalGrid_cover {a L h x : ℝ}
    (hh : 0 < h) (hx : x ∈ Icc a (a+L)) :
    ∃ i ∈ Finset.range (sargosIntervalGridCount L h),
      x ∈ Icc (a+(i:ℝ)*h) (a+(i:ℝ)*h+h) := by
  let q := (x-a)/h
  let i := ⌊q⌋₊
  have hq : 0 ≤ q := div_nonneg (by linarith only [hx.1]) hh.le
  have hqL : q ≤ L/h := div_le_div_of_nonneg_right (by linarith only [hx.2]) hh.le
  have hi : i ≤ ⌈L/h⌉₊ := (Nat.floor_mono hqL).trans (Nat.floor_le_ceil _)
  have hlo := Nat.floor_le hq
  have hup := Nat.lt_floor_add_one q
  have hqeq : q*h = x-a := by dsimp [q]; field_simp
  refine ⟨i,?_,?_,?_⟩
  · simpa only [Finset.mem_range,sargosIntervalGridCount,Nat.lt_succ_iff] using hi
  · have hm := mul_le_mul_of_nonneg_right hlo hh.le
    change a+(i:ℝ)*h ≤ x
    change (i:ℝ)*h ≤ q*h at hm
    linarith only [hm,hqeq]
  · have hm := mul_lt_mul_of_pos_right hup hh
    change x ≤ a+(i:ℝ)*h+h
    change q*h < ((i:ℝ)+1)*h at hm
    nlinarith only [hm,hqeq]

theorem sargosIntervalGrid_corner_bounds {a L h : ℝ}
    (hL : 0 ≤ L) (hh : 0 < h) {i : ℕ}
    (hi : i ∈ Finset.range (sargosIntervalGridCount L h)) :
    a ≤ a+(i:ℝ)*h ∧ a+(i:ℝ)*h ≤ a+L+h := by
  have hic : i ≤ ⌈L/h⌉₊ := by
    simpa only [Finset.mem_range,sargosIntervalGridCount,Nat.lt_succ_iff] using hi
  have hir : (i:ℝ) ≤ (⌈L/h⌉₊ : ℝ) := by exact_mod_cast hic
  have hceil := Nat.ceil_lt_add_one (div_nonneg hL hh.le)
  have hscale : (L/h)*h = L := by field_simp
  have hm := mul_lt_mul_of_pos_right (hir.trans_lt hceil) hh
  constructor
  · have hn : (0:ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith only [mul_nonneg hn hh.le]
  · nlinarith only [hm,hscale]

end TaoTrudgianYang2025
