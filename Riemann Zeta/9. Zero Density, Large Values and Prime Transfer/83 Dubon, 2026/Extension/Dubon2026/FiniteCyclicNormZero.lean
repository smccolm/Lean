import Dubon2026.FiniteCyclicH1Dimension

/-! Norm cancellation at sufficiently deep finite cyclic stages.
The cyclic/depth proof reviewed in anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 uses this elementary cancellation.
Here it feeds the pinned native periodic resolution, without importing
that repository's local-class model. DUB-17 still needs the original
unramified stages and continuous local comparison. -/

namespace Dubon2026
noncomputable section
open scoped BigOperators

/-- If the group order is divisible by the characteristic times a period
of the actual generator action, its original representation norm is zero. -/
theorem finite_cyclic_representation_norm_eq_zero
    {K G V : Type} [Field K] [Group G] [Fintype G]
    [AddCommGroup V] [Module K V] (T : Representation K G V)
    (p d : ℕ) [CharP K p] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hperiod : T g ^ d = 1) (hsize : p * d ∣ Fintype.card G) :
    T.norm = 0 := by
  classical
  have horder : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hcover : (Finset.range (Fintype.card G)).image (g ^ ·) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rw [← horder]
    exact (isOfFinOrder_of_finite g).mem_zpowers_iff_mem_range_orderOf.mp (hg x)
  have hsum : T.norm = ∑ j ∈ Finset.range (Fintype.card G), T g ^ j := by
    rw [Representation.norm, ← hcover, Finset.sum_image]
    · simp only [map_pow]
    · intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (horder ▸ Finset.mem_range.mp hi)
        (horder ▸ Finset.mem_range.mp hj) hij
  have hblocks (b : ℕ) : (∑ j ∈ Finset.range (d * b), T g ^ j) =
      b • ∑ j ∈ Finset.range d, T g ^ j := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add, pow_mul, hperiod, one_pow, one_mul]
  obtain ⟨b, hb⟩ := hsize
  rw [hsum, hb, Nat.mul_right_comm p d b, Nat.mul_comm (p * b) d, hblocks]
  rw [← Nat.cast_smul_eq_nsmul K, Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul, zero_smul]

/-- The required finite cyclic H1 dimension is attained at such a deep
stage, with the norm-zero premise discharged by the actual period. -/
theorem finite_cyclic_H1_finrank_eq_of_characteristic_period_dvd
    {K G : Type} [Field K] [CommGroup G] [Fintype G]
    (A : Rep K G) [FiniteDimensional K A] (p d : ℕ) [CharP K p] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hperiod : A.ρ g ^ d = 1) (hsize : p * d ∣ Fintype.card G) :
    Module.finrank K (groupCohomology A 1) = Module.finrank K A.ρ.invariants := by
  apply finite_cyclic_H1_finrank_eq_invariants_of_norm_zero A g hg
  exact finite_cyclic_representation_norm_eq_zero A.ρ p d g hg hperiod hsize

end
end Dubon2026
