import Dubon2026.RealExponentialZeros
import Mathlib.Data.Finset.Sort

/-! # Finite zero sets and cardinality for nontrivial real exponential sums -/

namespace Dubon2026

open Set

theorem realExponentialSum_zero_finset_card_lt {ι : Type*} (s : Finset ι)
    (c ω : ι → ℝ) (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hω : Set.InjOn ω s)
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, realExponentialSum s c ω x = 0) : Z.card < s.card := by
  classical
  by_contra h
  obtain ⟨u, hu, huc⟩ := Finset.exists_subset_card_eq (le_of_not_gt h)
  let x := u.orderEmbOfFin huc
  apply realExponentialSum_not_zero_at_all_ordered_points s c ω hs hc hω x x.strictMono
  intro i
  exact hZ _ (hu (u.orderEmbOfFin_mem huc i))

theorem finite_realExponentialSum_zeros {ι : Type*} (s : Finset ι)
    (c ω : ι → ℝ) (hs : s.Nonempty) (hc : ∀ i ∈ s, c i ≠ 0) (hω : Set.InjOn ω s) :
    {x : ℝ | realExponentialSum s c ω x = 0}.Finite := by
  by_contra h
  obtain ⟨Z, hZ, hcard⟩ := Set.Infinite.exists_subset_card_eq h s.card
  have hh := realExponentialSum_zero_finset_card_lt s c ω hs hc hω Z (fun x hx => hZ hx)
  omega

theorem realExponentialSum_filter_nonzero {ι : Type*} (s : Finset ι)
    (c ω : ι → ℝ) (x : ℝ) :
    realExponentialSum (s.filter (fun i => c i ≠ 0)) c ω x = realExponentialSum s c ω x := by
  classical
  unfold realExponentialSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · simp only [not_ne_iff.mp h, zero_mul]

end Dubon2026
