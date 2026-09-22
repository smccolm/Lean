import TaoTrudgianYang2025.BourgainSliceGeometry
import TaoTrudgianYang2025.BourgainPhysicalUpper
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithmic cardinality bounds for the actual source set and full slice

The interval bound uses the translated band, not a freely supplied auxiliary
set. Every logarithm used in a nonempty branch has a positive argument.
-/

open RiemannZeta.GuthMaynard Set
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_integer_slice_card_le {H T V u : ℝ}
    (hsize : 0 ≤ T+H) (hu : u ∈ Icc (-H) H) :
    ((bourgainIntegerSlice H T V u).card : ℝ) ≤ 2*(T+H)+1 := by
  have hsep := bourgainRealSlice_separated H T V u
  have h := oneSeparated_card_cast_le_interval_length_add_one
    (bourgainRealSlice H T V u) (by
      intro x hx y hy hxy
      simpa only [Real.dist_eq] using hsep x hx y hy hxy)
    (a := -(T+H)) (b := T+H) (by linarith) (bourgainRealSlice_bounds hu)
  rw [bourgainRealSlice_card] at h
  linarith

/-- The actual local height and shift window give a polynomial-size full slice. -/
theorem bourgain_local_slice_card_power {N L τ ε δ V u : ℝ}
    (hN : 1 ≤ N) (hNL : N ≤ L) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) (hu : u ∈ Icc (-(N^(ε/8))) (N^(ε/8))) :
    ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ≤
      9*N^(τ+δ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hLp : 0 < L := hNp.trans_le hNL
  have hH : 0 < N^(ε/8) := Real.rpow_pos_of_pos hNp _
  have hh := bourgain_shift_window_le_scale hN hε₈
  have hcard := bourgain_integer_slice_card_le
    (T := L+N^(ε/8)+1) (V := V) (by positivity) hu
  have hone : 1 ≤ N^(τ+δ) := hN.trans (hNL.trans hL)
  linarith

theorem bourgain_nonempty_log_card_nonneg {ι : Type*} (W : Finset ι)
    {N : ℝ} (hN : 1 < N) (hW : W.Nonempty) :
    0 ≤ Real.logb N (W.card : ℝ) := by
  apply Real.logb_nonneg hN
  exact_mod_cast hW.card_pos

/-- Exact finite compactness bounds for the full nonempty slice. -/
theorem bourgain_local_slice_log_card_bounds {N L τ ε δ V u : ℝ}
    (hN : 1 < N) (hNL : N ≤ L) (hε₈ : ε ≤ 8)
    (hL : L ≤ N^(τ+δ)) (hu : u ∈ Icc (-(N^(ε/8))) (N^(ε/8)))
    (hW : (bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).Nonempty) :
    0 ≤ Real.logb N ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ∧
      Real.logb N ((bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card : ℝ) ≤
        τ+δ+Real.logb N 9 := by
  refine ⟨bourgain_nonempty_log_card_nonneg _ hN hW, ?_⟩
  have hNp : 0 < N := zero_lt_one.trans hN
  have hWp : (0 : ℝ) <
      (bourgainIntegerSlice (N^(ε/8)) (L+N^(ε/8)+1) V u).card := by
    exact_mod_cast hW.card_pos
  calc
    _ ≤ Real.logb N (9*N^(τ+δ)) :=
      Real.logb_le_logb_of_le hN hWp (bourgain_local_slice_card_power hN.le hNL hε₈ hL hu)
    _ = τ+δ+Real.logb N 9 := by
      rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
        Real.logb_rpow hNp hN.ne']
      ring

/-- Subsets of the original actual ordinate set have the required bounded
logarithmic cardinality whenever the original height has the physical cap. -/
theorem bourgain_source_log_card_bounds (P : LargeValuePattern) (S : Finset ℝ)
    (hsub : S ⊆ P.ordinates) (hS : S.Nonempty) {τ δ : ℝ}
    (hone : 1 ≤ P.N^(τ+δ)) (hT : P.T ≤ P.N^(τ+δ)) :
    0 ≤ Real.logb P.N (S.card : ℝ) ∧
      Real.logb P.N (S.card : ℝ) ≤ τ+δ+Real.logb P.N 2 := by
  refine ⟨bourgain_nonempty_log_card_nonneg S P.one_lt_N hS, ?_⟩
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hSp : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hSc : (S.card : ℝ) ≤ P.ordinates.card := by exact_mod_cast Finset.card_le_card hsub
  have hbound : (S.card : ℝ) ≤ 2*P.N^(τ+δ) := by
    linarith [P.ordinate_card_cast_le]
  calc
    _ ≤ Real.logb P.N (2*P.N^(τ+δ)) := Real.logb_le_logb_of_le P.one_lt_N hSp hbound
    _ = τ+δ+Real.logb P.N 2 := by
      rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
        Real.logb_rpow hNp P.one_lt_N.ne']
      ring

end TaoTrudgianYang2025
