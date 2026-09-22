import TaoTrudgianYang2025.BourgainPhysicalComparison
import TaoTrudgianYang2025.BourgainLargeValueAlgebra

/-!
# Linking Huxley subdivision to the original height and logarithmic scales

The ninth-row parameter lies strictly inside the already proved local-height
range. The physical choice L=T/N^a has its two-sided power bounds, source
containment, and exact finite bin count proved explicitly.
-/

open Finset
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The row's chosen subdivision exponent leaves a genuine local-scale margin. -/
theorem bourgain_ninth_row_local_height_margin {σ τ : ℝ}
    (hσ : 3/4 < σ)
    (hlower : 16*σ-11 ≤ τ) (hupper : 20*σ+τ/3 ≤ 16) :
    0 ≤ max 0 (4*σ+4*τ/3-5) ∧
      1 < τ-max 0 (4*σ+4*τ/3-5) := by
  refine ⟨le_max_left _ _, ?_⟩
  rcases le_total 0 (4*σ+4*τ/3-5) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

/-- Both original-height power bounds transfer exactly through L=T/N^a.
A positive margin discharges N<=L rather than assuming it separately. -/
theorem bourgain_subdivision_physical_scales {N T τ a δ : ℝ}
    (hN : 1 < N) (ha : 0 ≤ a)
    (hmargin : 1+δ ≤ τ-a)
    (hTlo : N^(τ-δ) ≤ T) (hThi : T ≤ N^(τ+δ)) :
    0 < T/N^a ∧ N ≤ T/N^a ∧ T/N^a ≤ T ∧
      N^((τ-a)-δ) ≤ T/N^a ∧ T/N^a ≤ N^((τ-a)+δ) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hA : 0 < N^a := Real.rpow_pos_of_pos hNp _
  have hT : 0 < T := (Real.rpow_pos_of_pos hNp (τ-δ)).trans_le hTlo
  have hquotLo : N^((τ-a)-δ) ≤ T/N^a := by
    calc
      _ = N^(τ-δ)/N^a := by rw [← Real.rpow_sub hNp]; congr 1; ring
      _ ≤ _ := div_le_div_of_nonneg_right hTlo hA.le
  have hquotHi : T/N^a ≤ N^((τ-a)+δ) := by
    calc
      _ ≤ N^(τ+δ)/N^a := div_le_div_of_nonneg_right hThi hA.le
      _ = _ := by rw [← Real.rpow_sub hNp]; congr 1; ring
  have hNL : N ≤ T/N^a := by
    calc
      N = N^(1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N^((τ-a)-δ) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
      _ ≤ _ := hquotLo
  have hLT : T/N^a ≤ T := div_le_self hT.le (Real.one_le_rpow hN.le ha)
  exact ⟨div_pos hT hA, hNL, hLT, hquotLo, hquotHi⟩

/-- The actual source bin count is bounded by twice N^a, with no hidden
dependence on the original height. -/
theorem bourgain_subdivision_bin_count {N T a : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (ha : 0 ≤ a) :
    ((Finset.range (Nat.floor (T/(T/N^a))+1)).card : ℝ) ≤ 2*N^a := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hA : 0 < N^a := Real.rpow_pos_of_pos hNp _
  have hratio : T/(T/N^a) = N^a := by field_simp [hT.ne', hA.ne']
  have hfloor := Nat.floor_le hA.le
  have hone : 1 ≤ N^a := Real.one_le_rpow hN ha
  simp only [Finset.card_range, hratio, Nat.cast_add, Nat.cast_one]
  linarith

end TaoTrudgianYang2025
