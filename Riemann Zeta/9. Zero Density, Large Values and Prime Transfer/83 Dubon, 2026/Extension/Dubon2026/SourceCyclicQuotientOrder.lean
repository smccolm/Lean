import Dubon2026.SourceCyclicTorsionTransport

/-! DUB-17/18 -> all-level cyclic-root correspondence -> successive prime
quotients. A cyclic subgroup of order p*m contains an actual cyclic subgroup
of order p; quotienting by that kernel gives order m. Reuse native generator
orders and the first isomorphism theorem. The image-cardinality argument
adapts the Groups section of
S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceEllipticCyclicCount
noncomputable section

/-- Dividing the generator order constructs the actual kernel for a cyclic quotient step. -/
theorem exists_cyclic_subgroup_card_factor
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (hcyc : IsAddCyclic H) {p m : ℕ} (hm : m ≠ 0) (hcard : Nat.card H = p * m) :
    ∃ C : AddSubgroup G, C ≤ H ∧ IsAddCyclic C ∧ Nat.card C = p := by
  obtain ⟨P, hP⟩ := (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top H).mp hcyc
  have ho : addOrderOf P = p * m := by rw [← Nat.card_zmultiples, hP, hcard]
  refine ⟨AddSubgroup.zmultiples (m • P), AddSubgroup.zmultiples_le.mpr ?_,
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨m • P, rfl⟩, ?_⟩
  · exact H.nsmul_mem (hP ▸ AddSubgroup.mem_zmultiples P) m
  · rw [Nat.card_zmultiples, addOrderOf_nsmul_of_dvd hm (by rw [ho]; exact dvd_mul_left m p), ho]
    exact Nat.mul_div_cancel p (Nat.pos_of_ne_zero hm)

/-- The actual image cyclic subgroup has its order divided by the exact contained kernel. -/
theorem cyclic_image_card_of_kernel
    {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (φ : G →+ G')
    {p m : ℕ} (hp : p ≠ 0) (H : AddSubgroup G)
    (hcyc : IsAddCyclic H) (hcard : Nat.card H = p * m)
    (hker : φ.ker ≤ H) (hkercard : Nat.card φ.ker = p) :
    IsAddCyclic (H.map φ) ∧ Nat.card (H.map φ) = m := by
  letI := hcyc
  let ψ : H →+ H.map φ := φ.addSubgroupMap H
  have hψ : Function.Surjective ψ := φ.addSubgroupMap_surjective H
  refine ⟨isAddCyclic_of_surjective ψ hψ, ?_⟩
  have he : ψ.ker = φ.ker.addSubgroupOf H := by
    ext ⟨h, hh⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker,
      Subtype.ext_iff]
    rfl
  have hc : Nat.card ψ.ker = p := by
    rw [he, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hker).toEquiv, hkercard]
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv,
    hc, hcard, mul_comm] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp) h).symm

end
end Dubon2026.SourceEllipticCyclicCount
