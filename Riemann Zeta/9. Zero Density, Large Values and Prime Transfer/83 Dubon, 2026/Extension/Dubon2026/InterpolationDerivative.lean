import Dubon2026.HigherRolle
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Divided differences as a derivative at an intermediate point -/

namespace Dubon2026

open Set
open scoped BigOperators ContDiff

theorem polynomial_iteratedDeriv (n : ℕ) (p : Polynomial ℝ) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (Polynomial.derivative^[n] p).eval x := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have h : deriv (fun x => p.eval x) = fun x => p.derivative.eval x := funext (fun _ => p.deriv)
    rw [h, ih, Function.iterate_succ_apply]

theorem iteratedDeriv_interpolate (n : ℕ) (x : Fin (n + 1) → ℝ) (hx : Function.Injective x)
    (v : Fin (n + 1) → ℝ) (t : ℝ) :
    iteratedDeriv n (fun u => (Lagrange.interpolate Finset.univ x v).eval u) t =
      (n.factorial : ℝ) * ∑ i, v i / ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  classical
  rw [polynomial_iteratedDeriv]
  have h := Lagrange.eval_iterate_derivative_eq_sum (s := Finset.univ) hx.injOn
    (Lagrange.degree_interpolate_lt v hx.injOn) (k := n) (by simp) t
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.sub_self, Finset.powersetCard_zero,
    Finset.sum_singleton, Finset.prod_empty, mul_one,
    Lagrange.eval_interpolate_at_node v hx.injOn (Finset.mem_univ _)] using h

theorem exists_iteratedDeriv_eq_divided_difference (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Fin (n + 1) → ℝ) (hx : StrictMono x) :
    ∃ t ∈ Icc (x 0) (x (Fin.last n)), iteratedDeriv n f t =
      (n.factorial : ℝ) * ∑ i, f (x i) / ∏ j ∈ Finset.univ.erase i, (x i - x j) := by
  classical
  let p := Lagrange.interpolate Finset.univ x (fun i => f (x i))
  have hp : ContDiff ℝ ∞ (fun u => p.eval u) := by
    simpa only [Polynomial.aeval_def, Polynomial.eval₂_id] using p.contDiff_aeval ∞
  have hz (i : Fin (n + 1)) : f (x i) - p.eval (x i) = 0 := by
    rw [Lagrange.eval_interpolate_at_node _ hx.injective.injOn (Finset.mem_univ i), sub_self]
  obtain ⟨t, ht, hzero⟩ := exists_iteratedDeriv_eq_zero_of_ordered_zeros n
    (fun u => f u - p.eval u) (hf.sub hp) x hx hz
  have hn : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hd := iteratedDeriv_sub (n := n) (x := t)
    (hf.of_le hn).contDiffAt (hp.of_le hn).contDiffAt
  change iteratedDeriv n (fun u => f u - p.eval u) t =
    iteratedDeriv n f t - iteratedDeriv n (fun u => p.eval u) t at hd
  rw [hd, sub_eq_zero] at hzero
  exact ⟨t, ht, hzero.trans (iteratedDeriv_interpolate n x hx.injective _ t)⟩


theorem abs_divided_difference_le (n : ℕ) (x v : Fin (n + 1) → ℝ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsep : ∀ i j, i ≠ j → δ ≤ |x i - x j|) (hv : ∀ i, |v i| ≤ ε) :
    |(n.factorial : ℝ) * ∑ i, v i / ∏ j ∈ Finset.univ.erase i, (x i - x j)| ≤
      (n.factorial : ℝ) * (n + 1) * ε / δ ^ n := by
  classical
  have hden (i : Fin (n + 1)) : δ ^ n ≤ ∏ j ∈ Finset.univ.erase i, |x i - x j| := by
    have h := Finset.prod_le_prod (s := Finset.univ.erase i)
      (f := fun _ : Fin (n + 1) => δ) (g := fun j => |x i - x j|)
      (fun _ _ => hδ.le) (fun j hj => hsep i j (Finset.mem_erase.mp hj).1.symm)
    simpa using h
  have hterm (i : Fin (n + 1)) :
      |v i / ∏ j ∈ Finset.univ.erase i, (x i - x j)| ≤ ε / δ ^ n := by
    rw [abs_div, Finset.abs_prod]
    exact (div_le_div_of_nonneg_right (hv i) ((pow_pos hδ n).le.trans (hden i))).trans
      (div_le_div_of_nonneg_left hε (pow_pos hδ n) (hden i))
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n.factorial)]
  calc
    _ ≤ (n.factorial : ℝ) * ∑ i : Fin (n + 1), |v i / ∏ j ∈ Finset.univ.erase i, (x i - x j)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (n.factorial : ℝ) * ∑ _ : Fin (n + 1), ε / δ ^ n :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

theorem derivative_sublevel_spacing_constraint (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    {δ ε L : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsep : ∀ i j, i ≠ j → δ ≤ |x i - x j|) (hv : ∀ i, |f (x i)| ≤ ε)
    (hlower : ∀ t ∈ Icc (x 0) (x (Fin.last n)), L ≤ |iteratedDeriv n f t|) :
    L * δ ^ n ≤ (n.factorial : ℝ) * (n + 1) * ε := by
  obtain ⟨t, ht, heq⟩ := exists_iteratedDeriv_eq_divided_difference n f hf x hx
  have hb := hlower t ht
  rw [heq] at hb
  exact (le_div_iff₀ (pow_pos hδ n)).mp
    (hb.trans (abs_divided_difference_le n x (fun i => f (x i)) hδ hε hsep hv))

end Dubon2026
