import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

open Finset

def dyadicInterval (N : ℕ) : Finset ℕ := Ioc N (2 * N)

lemma convolution_support (N₁ N₂ n₁ n₂ : ℕ) (hn₁ : n₁ ∈ dyadicInterval N₁) (hn₂ : n₂ ∈ dyadicInterval N₂) :
    n₁ * n₂ ∈ Ioc (N₁ * N₂) (4 * N₁ * N₂) := by
  rw [dyadicInterval, Finset.mem_Ioc] at hn₁ hn₂
  rw [Finset.mem_Ioc]
  constructor
  · have h1 : (N₁ : ℝ) < (n₁ : ℝ) := Nat.cast_lt.mpr hn₁.1
    have h2 : (N₂ : ℝ) < (n₂ : ℝ) := Nat.cast_lt.mpr hn₂.1
    have hN1 : 0 ≤ (N₁ : ℝ) := Nat.cast_nonneg _
    have hN2 : 0 ≤ (N₂ : ℝ) := Nat.cast_nonneg _
    have res : (N₁ : ℝ) * (N₂ : ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by nlinarith
    exact Nat.cast_lt.mp (by exact_mod_cast res)
  · have h1 : (n₁ : ℝ) ≤ 2 * (N₁ : ℝ) := by exact_mod_cast hn₁.2
    have h2 : (n₂ : ℝ) ≤ 2 * (N₂ : ℝ) := by exact_mod_cast hn₂.2
    have hn1 : 0 ≤ (n₁ : ℝ) := Nat.cast_nonneg _
    have hn2 : 0 ≤ (n₂ : ℝ) := Nat.cast_nonneg _
    have res : (n₁ : ℝ) * (n₂ : ℝ) ≤ 4 * (N₁ : ℝ) * (N₂ : ℝ) := by nlinarith
    exact Nat.cast_le.mp (by exact_mod_cast res)
