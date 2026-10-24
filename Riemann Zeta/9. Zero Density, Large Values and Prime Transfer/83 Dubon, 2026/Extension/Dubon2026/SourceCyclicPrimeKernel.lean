import Dubon2026.SourceCyclicQuotientOrder

/-! DUB-17/18 -> all-level cyclic-root correspondence -> successive prime
quotients. The next kernel is the actual p-torsion inside the original cyclic
subgroup, so it does not depend on a choice of generator. Native bounds on
torsion in a finite cyclic group identify it with the previously constructed
subgroup of order p. The counting argument adapts the Groups section of
S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceEllipticCyclicCount
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The next literal kernel is the p-torsion subgroup inside the original cyclic group. -/
def cyclicPrimeKernel (H : AddSubgroup G) (p : ℕ) : AddSubgroup G :=
  H ⊓ AddSubgroup.torsionBy G (p : ℤ)

theorem mem_cyclicPrimeKernel (H : AddSubgroup G) (p : ℕ) (x : G) :
    x ∈ cyclicPrimeKernel H p ↔ x ∈ H ∧ p • x = 0 := by
  rw [cyclicPrimeKernel, AddSubgroup.mem_inf, AddSubgroup.torsionBy.nsmul_iff]

/-- Any contained subgroup of order p is exactly the intrinsic p-torsion kernel. -/
theorem cyclicPrimeKernel_eq_of_card
    (H : AddSubgroup G) [IsAddCyclic H] [Finite H]
    {p : ℕ} (hp : 0 < p) {C : AddSubgroup G} (hCH : C ≤ H) (hC : Nat.card C = p) :
    cyclicPrimeKernel H p = C := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let T : Finset H := Finset.univ.filter fun x : H => p • x = 0
  have hT : T.card ≤ p := IsAddCyclic.card_nsmul_eq_zero_le hp
  have he : (C.addSubgroupOf H : Set H).toFinset = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Set.mem_toFinset, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf] at hx
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
      have hk := card_nsmul_eq_zero' (G := C) (x := ⟨(x : G), hx⟩)
      rw [hC] at hk
      exact congrArg Subtype.val hk
    · rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      change T.card ≤ Nat.card (C.addSubgroupOf H)
      rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCH).toEquiv, hC]
      exact hT
  ext x
  rw [mem_cyclicPrimeKernel]
  constructor
  · rintro ⟨hxH, hx⟩
    have ht : (⟨x, hxH⟩ : H) ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext hx
    rw [← he, Set.mem_toFinset, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf] at ht
    exact ht
  · intro hx
    refine ⟨hCH hx, ?_⟩
    have hk := card_nsmul_eq_zero' (G := C) (x := ⟨x, hx⟩)
    rw [hC] at hk
    exact congrArg Subtype.val hk

/-- The intrinsic kernel has the required cyclic structure and exact prime-factor order. -/
theorem cyclicPrimeKernel_cyclic_card
    (H : AddSubgroup G) (hcyc : IsAddCyclic H)
    {p m : ℕ} (hp : p ≠ 0) (hm : m ≠ 0) (hcard : Nat.card H = p * m) :
    IsAddCyclic (cyclicPrimeKernel H p) ∧ Nat.card (cyclicPrimeKernel H p) = p := by
  letI := hcyc
  letI : Finite H := Nat.finite_of_card_ne_zero (hcard ▸ mul_ne_zero hp hm)
  obtain ⟨C, hCH, hCc, hCn⟩ := exists_cyclic_subgroup_card_factor H hcyc hm hcard
  rw [cyclicPrimeKernel_eq_of_card H (Nat.pos_of_ne_zero hp) hCH hCn]
  exact ⟨hCc, hCn⟩

end
end Dubon2026.SourceEllipticCyclicCount
