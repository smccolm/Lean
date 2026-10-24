import Dubon2026.SourceCyclicTorsionTransport
import Dubon2026.SourceEllipticSubgroupSpecializationTransport

/-! DUB-17/18 -> exceptional place census. The native subgroup lattice
equivalence restricts to actual cyclic subgroups of the prescribed order.
Quadratic elliptic identities give the required permutation periods;
the existing subgroup-negation theorem handles the quartic action. -/
namespace Dubon2026.SourceEllipticExceptional
open SourceEllipticCyclicCount SourceEllipticReduction
noncomputable section
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An actual point-group equivalence acts on cyclic subgroups of order N. -/
def cyclicSubgroupEquiv (N : ℕ) (e : A ≃+ B) :
    {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N} ≃
      {H : AddSubgroup B // IsAddCyclic H ∧ Nat.card H = N} :=
  Equiv.subtypeEquiv e.mapAddSubgroup.toEquiv fun H => by
    change (IsAddCyclic H ∧ Nat.card H = N) ↔
      (IsAddCyclic (H.map e.toAddMonoidHom) ∧ Nat.card (H.map e.toAddMonoidHom) = N)
    constructor
    · intro h
      have hc := isAddCyclic_map_and_card_of_injective N e.toAddMonoidHom e.injective h
      exact ⟨hc.1, hc.2.1⟩
    · intro h
      have hc := isAddCyclic_map_and_card_of_injective N e.symm.toAddMonoidHom e.symm.injective h
      have he : (H.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = H :=
        e.mapAddSubgroup.symm_apply_apply H
      rw [he] at hc
      exact ⟨hc.1, hc.2.1⟩

theorem cyclicSubgroupEquiv_square (N : ℕ) (e : A ≃+ A)
    (he : ∀ x, e (e x) = -x) : (cyclicSubgroupEquiv N e) ^ 2 = 1 := by
  ext H : 1
  apply Subtype.ext
  change (H.val.map e.toAddMonoidHom).map e.toAddMonoidHom = H.val
  rw [AddSubgroup.map_map]
  have hcomp : e.toAddMonoidHom.comp e.toAddMonoidHom = -(AddMonoidHom.id A) :=
    AddMonoidHom.ext he
  rw [hcomp, subgroup_map_neg_eq]

theorem cyclicSubgroupEquiv_cube (N : ℕ) (e : A ≃+ A)
    (he : ∀ x, e (e x) + e x + x = 0) : (cyclicSubgroupEquiv N e) ^ 3 = 1 := by
  have hpoint (x : A) : e (e (e x)) = x := by
    have h := he (e x)
    rw [add_assoc, eq_neg_of_add_eq_zero_left (he x)] at h
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
  ext H : 1
  apply Subtype.ext
  change ((H.val.map e.toAddMonoidHom).map e.toAddMonoidHom).map e.toAddMonoidHom = H.val
  rw [AddSubgroup.map_map, AddSubgroup.map_map]
  have hcomp : (e.toAddMonoidHom.comp e.toAddMonoidHom).comp e.toAddMonoidHom =
      AddMonoidHom.id A := AddMonoidHom.ext hpoint
  rw [hcomp, AddSubgroup.map_id]

theorem cyclicSubgroupEquiv_fixed_card (N : ℕ) (e : A ≃+ A) :
    Nat.card {H // cyclicSubgroupEquiv N e H = H} =
      Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N ∧
        H.map e.toAddMonoidHom = H} := by
  apply Nat.card_congr
  exact {
    toFun := fun H => ⟨H.val.val, H.val.property.1, H.val.property.2,
      congrArg Subtype.val H.property⟩
    invFun := fun H => ⟨⟨H.val, H.property.1, H.property.2.1⟩,
      Subtype.ext H.property.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end
end Dubon2026.SourceEllipticExceptional
