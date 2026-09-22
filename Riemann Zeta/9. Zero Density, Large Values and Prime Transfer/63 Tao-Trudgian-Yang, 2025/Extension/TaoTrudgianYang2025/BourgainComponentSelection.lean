import TaoTrudgianYang2025.BourgainSubdivisionGrid

/-!
# Finite common-component selection with the exact counting loss

Weighted pigeonholing selects an actual fiber of the amplitude index.
The small-component contribution and number of available bands remain explicit.
-/

open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- A common finite index carries at least one counting share of a weighted
family. The fiber consists of the original indices, not copied objects. -/
theorem bourgain_exists_heavy_component_fiber {ι : Type*} (I : Finset ι)
    (w : ι → ℝ) (q : ι → ℕ) {J : ℕ} (hJ : 0 < J)
    (hq : ∀ i ∈ I, q i ∈ Finset.range J) :
    ∃ q₀ ∈ Finset.range J,
      (∑ i ∈ I, w i) ≤ (J : ℝ) * ∑ i ∈ I.filter (fun i => q i = q₀), w i := by
  let mass := fun j => ∑ i ∈ I.filter (fun i => q i = j), w i
  obtain ⟨q₀, hq₀, hmax⟩ := Finset.exists_max_image (Finset.range J) mass
    (Finset.nonempty_range_iff.mpr hJ.ne')
  refine ⟨q₀, hq₀, ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to hq w]
  calc
    _ ≤ ∑ _j ∈ Finset.range J, mass q₀ := Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = _ := by simp [mass]

/-- Partition at the actual small-component bound and select a common
amplitude index on its complement. The small cost uses all original bins;
the large cost is the exact band count times the retained fiber mass. -/
theorem bourgain_small_large_component_selection {ι : Type*} (I : Finset ι)
    (R w : ι → ℝ) (q : ι → ℕ) {F K : ℝ} (hF : 0 ≤ F) (hK : 0 ≤ K)
    {J : ℕ} (hJ : 0 < J)
    (hpack : ∀ i ∈ I, F < R i → R i ≤ K*w i)
    (hq : ∀ i ∈ I, F < R i → q i ∈ Finset.range J) :
    ∃ q₀ ∈ Finset.range J,
      let A := I.filter (fun i => F < R i ∧ q i = q₀)
      (∑ i ∈ I, R i) ≤ (I.card : ℝ)*F + K*(J : ℝ)*∑ i ∈ A, w i := by
  let G := I.filter (fun i => F < R i)
  obtain ⟨q₀, hq₀, hheavy⟩ := bourgain_exists_heavy_component_fiber G w q hJ
    (fun i hi => hq i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  refine ⟨q₀, hq₀, ?_⟩
  have hsplit : (∑ i ∈ I, R i) ≤ (I.card : ℝ)*F + K*∑ i ∈ G, w i := by
    calc
      _ ≤ ∑ i ∈ I, (F + if F < R i then K*w i else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs with h
        · linarith [hpack i hi h]
        · exact (le_of_not_gt h).trans (by simp)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.sum_filter]
        rw [Finset.mul_sum]
  have hfiber : G.filter (fun i => q i = q₀) =
      I.filter (fun i => F < R i ∧ q i = q₀) := by
    ext i
    simp [G, and_assoc]
  rw [hfiber] at hheavy
  apply hsplit.trans
  calc
    _ ≤ (I.card : ℝ)*F + K*((J : ℝ)*∑ i ∈ I.filter (fun i => F < R i ∧ q i = q₀), w i) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hheavy hK)
    _ = _ := by ring

end TaoTrudgianYang2025
