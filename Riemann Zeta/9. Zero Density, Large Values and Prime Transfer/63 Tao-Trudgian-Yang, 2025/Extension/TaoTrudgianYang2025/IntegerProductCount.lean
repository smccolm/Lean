import TaoTrudgianYang2025.PrimitiveDivisorGrowth

/-! Actual integer factor pairs with positive first factor inject into the divisors
of the absolute value of their nonzero product. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem positive_integer_product_pairs_card_le
    (S : Finset (ℤ × ℤ)) {m : ℤ} (hm : m ≠ 0)
    (hpos : ∀ p ∈ S, 0 < p.1)
    (hprod : ∀ p ∈ S, p.1*p.2 = m) :
    S.card ≤ m.natAbs.divisors.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun p => p.1.natAbs)
  · intro p hp
    apply Nat.mem_divisors.mpr
    constructor
    · rw [← hprod p hp,Int.natAbs_mul]
      exact dvd_mul_right _ _
    · exact Int.natAbs_ne_zero.mpr hm
  · intro p hp q hq he
    have hfirst : p.1 = q.1 := by
      rcases Int.natAbs_eq_natAbs_iff.mp he with heq | hneg
      · exact heq
      · have hp0 := hpos p hp
        have hq0 := hpos q hq
        omega
    apply Prod.ext hfirst
    apply mul_left_cancel₀ (ne_of_gt (hpos p hp))
    calc
      p.1*p.2 = m := hprod p hp
      _ = q.1*q.2 := (hprod q hq).symm
      _ = p.1*q.2 := by rw [hfirst]

theorem exists_positive_integer_product_pairs_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (ℤ × ℤ)) (m : ℤ) (M : ℝ),
      m ≠ 0 → (m.natAbs:ℝ) ≤ M →
      (∀ p ∈ S, 0 < p.1) → (∀ p ∈ S, p.1*p.2 = m) →
      (S.card:ℝ) ≤ C*M^ε := by
  obtain ⟨C,hC,hdiv⟩ := RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  refine ⟨C,hC,?_⟩
  intro S m M hm hM hpos hprod
  calc
    _ ≤ (m.natAbs.divisors.card:ℝ) := by
      exact_mod_cast positive_integer_product_pairs_card_le S hm hpos hprod
    _ ≤ C*(m.natAbs:ℝ)^ε := hdiv _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hm))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hM hε.le) hC.le

end TaoTrudgianYang2025

