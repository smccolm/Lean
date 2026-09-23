import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Literal finite independent-sign samples, with multiplicities retained. -/

namespace TaoTrudgianYang2025

def finiteSignSamples {α : Type*} [AddGroup α] : List α → List α
  | [] => [0]
  | z::v => (finiteSignSamples v).map (fun w => w+z) ++
      (finiteSignSamples v).map (fun w => w-z)

theorem finiteSignSamples_length {α : Type*} [AddGroup α] (v : List α) :
    (finiteSignSamples v).length = 2^v.length := by
  induction v with
  | nil => simp [finiteSignSamples]
  | cons z v ih => simp [finiteSignSamples,ih,pow_succ]; omega

theorem finiteSignSamples_map {α β : Type*} [AddGroup α] [AddGroup β]
    (f : α →+ β) (v : List α) :
    (finiteSignSamples v).map f = finiteSignSamples (v.map f) := by
  induction v with
  | nil => simp [finiteSignSamples]
  | cons z v ih =>
    simp only [List.map_cons,finiteSignSamples,List.map_append,List.map_map,
      Function.comp_def,map_add,map_sub]
    rw [← ih]
    simp only [List.map_map,Function.comp_def]

theorem complex_sign_second_pair (w z : ℂ) :
    Complex.normSq (w+z)+Complex.normSq (w-z) =
      2*Complex.normSq w+2*Complex.normSq z := by
  rw [Complex.normSq_add,Complex.normSq_sub]
  ring

theorem complex_sign_fourth_pair (w z : ℂ) :
    Complex.normSq (w+z)^2+Complex.normSq (w-z)^2 ≤
      2*Complex.normSq w^2+12*Complex.normSq w*Complex.normSq z+
        2*Complex.normSq z^2 := by
  have h := Complex.re_sq_le_normSq (w*starRingEnd ℂ z)
  rw [Complex.normSq_mul,Complex.normSq_conj] at h
  rw [Complex.normSq_add,Complex.normSq_sub]
  nlinarith

end TaoTrudgianYang2025
