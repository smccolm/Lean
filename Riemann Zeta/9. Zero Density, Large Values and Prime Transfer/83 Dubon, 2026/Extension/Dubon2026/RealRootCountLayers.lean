import Dubon2026.DerivativeGcdLayers

/-! # Multiplicity-weighted real interval counts are sums of distinct-root layers -/

namespace Dubon2026

open Polynomial

noncomputable section

/-- Actual real roots in the open interval, retaining their algebraic multiplicities. -/
def realPolynomialRootCount (P : ℝ[X]) (l u : ℝ) : ℕ :=
  (P.roots.filter (fun t => l < t ∧ t < u)).card

/-- Actual distinct real roots in the same interval. -/
def realPolynomialDistinctRootCount (P : ℝ[X]) (l u : ℝ) : ℕ :=
  (P.roots.toFinset.filter (fun t => l < t ∧ t < u)).card

theorem realPolynomialRootCount_eq_sum (P : ℝ[X]) (l u : ℝ) :
    realPolynomialRootCount P l u =
      ∑ t ∈ P.roots.toFinset.filter (fun t => l < t ∧ t < u), P.rootMultiplicity t := by
  classical
  rw [realPolynomialRootCount, ← Multiset.toFinset_sum_count_eq, Multiset.toFinset_filter]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Multiset.count_filter_of_pos (p := fun t => l < t ∧ t < u)
    (Finset.mem_filter.mp ht).2, Polynomial.count_roots]

theorem derivativeGcdLayer_roots_subset {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) :
    (derivativeGcdLayer P k).roots.toFinset ⊆ P.roots.toFinset := by
  classical
  intro t ht
  rw [Multiset.mem_toFinset, mem_derivativeGcdLayer_roots hP] at ht
  rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
  exact lt_of_le_of_lt (Nat.zero_le k) ht

theorem distinct_layer_count_eq_sum {P : ℝ[X]} (hP : P ≠ 0) (k : ℕ) (l u : ℝ) :
    realPolynomialDistinctRootCount (derivativeGcdLayer P k) l u =
      ∑ t ∈ P.roots.toFinset.filter (fun t => l < t ∧ t < u),
        if t ∈ (derivativeGcdLayer P k).roots then 1 else 0 := by
  classical
  rw [Finset.sum_boole]
  unfold realPolynomialDistinctRootCount
  congr 1
  ext t
  simp only [Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · rintro ⟨ht, hlt, htu⟩
    exact ⟨⟨by simpa only [Multiset.mem_toFinset] using
      derivativeGcdLayer_roots_subset hP k (by simpa only [Multiset.mem_toFinset] using ht),
      hlt, htu⟩, ht⟩
  · rintro ⟨⟨_, hlt, htu⟩, ht⟩
    exact ⟨ht, hlt, htu⟩

/-- The multiplicity reduction in the repeated-GCD part of the Sturm procedure. -/
theorem realPolynomialRootCount_eq_sum_distinct_layers {P : ℝ[X]} (hP : P ≠ 0) (l u : ℝ) :
    realPolynomialRootCount P l u = ∑ k ∈ Finset.range P.natDegree,
      realPolynomialDistinctRootCount (derivativeGcdLayer P k) l u := by
  classical
  rw [realPolynomialRootCount_eq_sum]
  simp_rw [distinct_layer_count_eq_sum hP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact rootMultiplicity_eq_sum_derivativeGcdLayers hP t

end

end Dubon2026
