import Dubon2026.TorusEnergy
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Exact Abel summation for the actual coefficient square sum -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

/-- The genuine positive-index cumulative coefficient square sum at a real cutoff. -/
def squareSummatory (a : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖a n‖ ^ 2

theorem squareSummatory_nat (a : ℕ → ℂ) (N : ℕ) :
    squareSummatory a N = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rw [squareSummatory, Nat.floor_natCast]

theorem zero_extended_square_sum (a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, if n = 0 then (0 : ℝ) else ‖a n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have he : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [he, Finset.sum_insert (by simp), if_pos rfl, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  exact if_neg (by have hh := Finset.mem_Icc.mp hn; omega)

theorem squareSummatory_integrable_power (a : ℕ → ℂ) (N : ℕ) (r : ℝ) :
    IntegrableOn (fun x : ℝ => squareSummatory a x * x ^ r) (Icc 1 (N : ℝ)) := by
  have hc : ContinuousOn (fun x : ℝ => x ^ r) (Icc 1 (N : ℝ)) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x r (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hh := integrableOn_mul_sum_Icc (fun n => ‖a n‖ ^ 2) (m := 1)
    (a := (1 : ℝ)) (b := (N : ℝ)) (by norm_num) hc.integrableOn_Icc
  simpa only [squareSummatory, mul_comm] using hh

/-- The Abel formula is valid also at sigma=0; no exceptional exponent is needed. -/
theorem coefficientEnergy_abel (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    coefficientEnergy a N σ = squareSummatory a N * (N : ℝ) ^ (-2 * σ) +
      2 * σ * ∫ x in Ioc (1 : ℝ) N, squareSummatory a x * x ^ (-2 * σ - 1) := by
  let b : ℕ → ℝ := fun n => if n = 0 then 0 else ‖a n‖ ^ 2
  have hd (x : ℝ) (hx : x ∈ Icc (1 : ℝ) N) :
      HasDerivAt (fun t : ℝ => t ^ (-2 * σ)) ((-2 * σ) * x ^ (-2 * σ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))
  have hc : ContinuousOn (fun x : ℝ => (-2 * σ) * x ^ (-2 * σ - 1)) (Icc 1 (N : ℝ)) := by
    apply continuousOn_const.mul
    intro x hx
    exact (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hdi : IntegrableOn (deriv (fun t : ℝ => t ^ (-2 * σ))) (Icc 1 (N : ℝ)) :=
    hc.integrableOn_Icc.congr_fun (fun x hx => (hd x hx).deriv.symm) measurableSet_Icc
  have hh := sum_mul_eq_sub_sub_integral_mul' b hN
    (fun x hx => (hd x (by simpa only [Nat.cast_one] using hx)).differentiableAt)
    (by simpa only [Nat.cast_one] using hdi)
  have hs (M : ℕ) : (∑ n ∈ Finset.Icc 0 M, b n) = ∑ n ∈ Finset.Icc 1 M, ‖a n‖ ^ 2 :=
    zero_extended_square_sum a M
  simp only [hs, Nat.cast_one, Real.one_rpow, Finset.Icc_self, Finset.sum_singleton, one_mul] at hh
  have hleft : (∑ n ∈ Finset.Ioc 1 N, (n : ℝ) ^ (-2 * σ) * b n) =
      coefficientEnergy a N σ - ‖a 1‖ ^ 2 := by
    have he : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    rw [coefficientEnergy, he, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.one_rpow, mul_one, add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have hh := Finset.mem_Ioc.mp hn; omega
    simp only [b, if_neg hn0, mul_comm]
  have hint : (∫ x in Ioc (1 : ℝ) N, deriv (fun t : ℝ => t ^ (-2 * σ)) x *
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖a n‖ ^ 2) =
      (-2 * σ) * ∫ x in Ioc (1 : ℝ) N, squareSummatory a x * x ^ (-2 * σ - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(hd x ⟨hx.1.le, hx.2⟩).deriv]
    simp only [squareSummatory]
    ring
  rw [hleft, hint] at hh
  rw [squareSummatory_nat]
  linarith

end

end Dubon2026
