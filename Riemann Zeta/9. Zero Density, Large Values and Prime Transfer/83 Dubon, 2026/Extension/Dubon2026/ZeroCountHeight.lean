import Dubon2026.UniformLocalZeroCount

/-! # Monotonicity and bounded unit changes of the genuine symmetric zero count -/

namespace Dubon2026

open Set
open scoped BigOperators

theorem verticalZeroCount_mono_height {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {T U : ℝ} (hTU : T ≤ U) :
    verticalZeroCount a N hN ha l u T ≤ verticalZeroCount a N hN ha l u U := by
  apply Finset.sum_le_sum_of_subset
  intro s hs
  rw [mem_zerosInOpenRectangleFinset] at hs ⊢
  exact ⟨hs.1, hs.2.1, hs.2.2.1.trans_le hTU, hs.2.2.2⟩

theorem sum_union_le_sum_add_of_nonneg {X : Type*} [DecidableEq X]
    (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (S T : Finset X) :
    (∑ x ∈ S ∪ T, f x) ≤ (∑ x ∈ S, f x) + ∑ x ∈ T, f x := by
  have he := Finset.sum_union_inter (f := f) (s₁ := S) (s₂ := T)
  have hn : 0 ≤ ∑ x ∈ S ∩ T, f x := Finset.sum_nonneg (fun x _ => hf x)
  linarith

theorem exists_verticalZeroCount_unit_increment_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T U : ℝ, 0 ≤ T → T ≤ U → U ≤ T + 1 →
      (verticalZeroCount a N hN ha l u U : ℝ) ≤
        (verticalZeroCount a N hN ha l u T : ℝ) + B := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_uniform_unit_strip_zero_bound hN ha l u
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro T U hT _hTU hU
  let A := zerosInOpenRectangleFinset a N hN ha l u U
  let D := zerosInOpenRectangleFinset a N hN ha l u T
  let P := A.filter (fun s : ℂ => T ≤ s.im)
  let M := A.filter (fun s : ℂ => s.im ≤ -T)
  let f := fun s : ℂ => (zeroMultiplicity a N s : ℝ)
  have hf (s : ℂ) : 0 ≤ f s := Nat.cast_nonneg _
  have hP : ∑ s ∈ P, f s ≤ C := by
    apply hb T P
    intro s hs
    obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hs
    obtain ⟨hl, hu, ht, hz⟩ := (mem_zerosInOpenRectangleFinset a N hN ha l u U s).mp hs
    refine ⟨hl.le, hu.le, abs_le.mpr ?_, hz⟩
    have him := le_abs_self s.im
    constructor <;> linarith
  have hM : ∑ s ∈ M, f s ≤ C := by
    apply hb (-T) M
    intro s hs
    obtain ⟨hs, hi⟩ := Finset.mem_filter.mp hs
    obtain ⟨hl, hu, ht, hz⟩ := (mem_zerosInOpenRectangleFinset a N hN ha l u U s).mp hs
    refine ⟨hl.le, hu.le, abs_le.mpr ?_, hz⟩
    have him := neg_abs_le s.im
    constructor <;> linarith
  have hsub : A ⊆ D ∪ P ∪ M := by
    intro s hs
    by_cases hp : T ≤ s.im
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hp⟩))
    by_cases hm : s.im ≤ -T
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hm⟩)
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    rw [mem_zerosInOpenRectangleFinset] at hs ⊢
    exact ⟨hs.1, hs.2.1, abs_lt.mpr ⟨lt_of_not_ge hm, lt_of_not_ge hp⟩, hs.2.2.2⟩
  have hsum : (∑ s ∈ A, f s) ≤ (∑ s ∈ D, f s) + 2 * C := by
    have h₁ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => hf s)
    have h₂ := sum_union_le_sum_add_of_nonneg f hf (D ∪ P) M
    have h₃ := sum_union_le_sum_add_of_nonneg f hf D P
    linarith
  simpa only [A, D, f, verticalZeroCount, Nat.cast_sum] using hsum

end Dubon2026
