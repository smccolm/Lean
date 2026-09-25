import TaoTrudgianYang2025.RobertSargosPlaneAveraging

/-! Exact multiplicities of signed differences of bounded shifts.
Both signs and the zero difference are counted, not merely majorized. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem card_positive_shift_difference (N k : ℕ) :
    ((Finset.range N ×ˢ Finset.range N).filter
      (fun p => (p.1:ℤ)-p.2 = k)).card = N-k := by
  classical
  rw [← Finset.card_range (N-k)]
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    have ht := Finset.mem_filter.mp hp
    have hm := Finset.mem_product.mp ht.1
    have h₁ := Finset.mem_range.mp hm.1
    have h₂ := Finset.mem_range.mp hm.2
    apply Finset.mem_range.mpr
    omega
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    apply Prod.ext <;> omega
  · intro t ht
    have ht' := Finset.mem_range.mp ht
    refine ⟨(t+k,t),?_,rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor <;> apply Finset.mem_range.mpr <;> omega
    · dsimp only
      omega

theorem card_shift_difference_neg (N : ℕ) (q : ℤ) :
    ((Finset.range N ×ˢ Finset.range N).filter
      (fun p => (p.1:ℤ)-p.2 = -q)).card =
      ((Finset.range N ×ˢ Finset.range N).filter
        (fun p => (p.1:ℤ)-p.2 = q)).card := by
  classical
  apply Finset.card_bij (fun p _ => p.swap)
  · intro p hp
    have ht := Finset.mem_filter.mp hp
    have hm := Finset.mem_product.mp ht.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hm.2,hm.1⟩,by dsimp only [Prod.swap]; omega⟩
  · intro p hp z hz he
    exact Prod.swap_injective he
  · intro p hp
    have ht := Finset.mem_filter.mp hp
    have hm := Finset.mem_product.mp ht.1
    refine ⟨p.swap,?_,Prod.swap_swap p⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hm.2,hm.1⟩,by dsimp only [Prod.swap]; omega⟩

theorem card_signed_shift_difference (N : ℕ) (q : ℤ) :
    ((Finset.range N ×ˢ Finset.range N).filter
      (fun p => (p.1:ℤ)-p.2 = q)).card = N-q.natAbs := by
  have he : q.natAbs = ((q.natAbs:ℤ)).natAbs := by simp only [Int.natAbs_natCast]
  rcases Int.natAbs_eq_natAbs_iff.mp he with hp | hn
  · rw [hp]
    exact card_positive_shift_difference N q.natAbs
  · rw [hn,card_shift_difference_neg]
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using
      card_positive_shift_difference N q.natAbs

theorem sum_signed_shift_differences (N : ℕ) (f : ℤ → ℝ) :
    (∑ s ∈ Finset.range N, ∑ t ∈ Finset.range N, f ((s:ℤ)-t)) =
      ∑ q ∈ Finset.Ioo (-(N:ℤ)) N, ((N-q.natAbs:ℕ):ℝ)*f q := by
  classical
  have hmap : ∀ p ∈ Finset.range N ×ˢ Finset.range N,
      (p.1:ℤ)-p.2 ∈ Finset.Ioo (-(N:ℤ)) N := by
    intro p hp
    have ht := Finset.mem_product.mp hp
    have hs := Finset.mem_range.mp ht.1
    have ht' := Finset.mem_range.mp ht.2
    apply Finset.mem_Ioo.mpr
    omega
  rw [← Finset.sum_product (Finset.range N) (Finset.range N)
    (fun p : ℕ × ℕ => f ((p.1:ℤ)-p.2)),
    ← Finset.sum_fiberwise_of_maps_to' hmap f]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.sum_const,nsmul_eq_mul,card_signed_shift_difference]

end TaoTrudgianYang2025
