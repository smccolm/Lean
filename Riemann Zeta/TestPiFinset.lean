import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Asymptotics
import Mathlib.Tactic

open Complex Finset
open scoped BigOperators

lemma k_divisor_function_bound_one (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
  (((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).filter (fun p => (∏ x : Fin k, p x) = 1)).card : ℝ) ≤ 1 * (1 : ℝ)^ε := by
  have h1 : (1 : ℝ)^ε = 1 := Real.one_rpow ε
  rw [h1, mul_one]
  have h2 : ((Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).filter (fun p => (∏ x : Fin k, p x) = 1)).card ≤
             (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).card := Finset.card_filter_le _ _
  have h3 : (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 1)).card = ∏ x : Fin k, (Finset.Ioc 1 1).card := by
    exact Fintype.card_piFinset _
  rw [h3] at h2
  have h4 : ∏ x : Fin k, (Finset.Ioc 1 1).card = ∏ x : Fin k, 0 := by
    apply Finset.prod_congr rfl
    intro x _
    exact Nat.sub_self 1
  rw [h4] at h2
  cases k with
  | zero =>
    rw [Finset.prod_empty] at h2
    exact_mod_cast h2
  | succ k' =>
    have h_prod_zero : ∏ x : Fin (k' + 1), 0 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (k' + 1)))
      rfl
    rw [h_prod_zero] at h2
    have h5 : ((Fintype.piFinset (fun _ => Ioc 1 1)).filter (fun p => ∏ x, p x = 1)).card = 0 := by linarith
    rw [h5]
    norm_num
