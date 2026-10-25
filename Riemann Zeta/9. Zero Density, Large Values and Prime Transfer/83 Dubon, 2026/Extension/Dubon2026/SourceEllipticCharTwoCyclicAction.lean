import Dubon2026.SourceEllipticCharTwoSignExponent
import Dubon2026.SourceEllipticCyclicStabilizerRelation

/-! DUB-17/18 -> weighted characteristic-two exceptional census. The
actual stabilizer acts on actual cyclic order-N subgroups. Reuse its native
point homomorphism and Mathlib's pointwise subgroup action, then factor
through the already constructed sign quotient. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer Pointwise
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- The actual cyclic order-N subgroups of the exceptional curve. -/
abbrev CyclicSubgroup (K : Type*) [Field K] [DecidableEq K] (N : ℕ) :=
  {H : AddSubgroup (ofJ0 K).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}

/-- The actual stabilizer action transported through its native point maps. -/
scoped instance stabilizerPointAction :
    DistribMulAction (MulAction.stabilizer (VariableChange K) (ofJ0 K)) (ofJ0 K).toAffine.Point :=
  DistribMulAction.compHom _ (stabilizerPointHom (ofJ0 K))

theorem smul_addSubgroup_eq_map
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K))
    (H : AddSubgroup (ofJ0 K).toAffine.Point) :
    g • H = H.map (stabilizerPointHom (ofJ0 K) g).toAddMonoidHom := by
  apply SetLike.coe_injective
  rw [AddSubgroup.coe_pointwise_smul, AddSubgroup.coe_map]
  rfl

theorem cyclic_smul_properties
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K))
    (N : ℕ) (H : CyclicSubgroup K N) :
    IsAddCyclic (g • H.val : AddSubgroup (ofJ0 K).toAffine.Point) ∧
      Nat.card (g • H.val : AddSubgroup (ofJ0 K).toAffine.Point) = N := by
  rw [smul_addSubgroup_eq_map]
  haveI := H.property.1
  let e := H.val.equivMapOfInjective (stabilizerPointHom (ofJ0 K) g).toAddMonoidHom
    (stabilizerPointHom (ofJ0 K) g).injective
  exact ⟨isAddCyclic_of_surjective e.toAddMonoidHom e.surjective,
    (AddSubgroup.card_map_of_injective (stabilizerPointHom (ofJ0 K) g).injective).trans H.property.2⟩

/-- The induced action on cyclic subgroups of the prescribed order. -/
scoped instance cyclicStabilizerAction (N : ℕ) :
    MulAction (MulAction.stabilizer (VariableChange K) (ofJ0 K)) (CyclicSubgroup K N) where
  smul g H := ⟨g • H.val, cyclic_smul_properties g N H⟩
  one_smul H := Subtype.ext (one_smul _ H.val)
  mul_smul g h H := Subtype.ext (mul_smul g h H.val)

theorem cyclic_smul_val {N : ℕ}
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K)) (H : CyclicSubgroup K N) :
    (g • H : CyclicSubgroup K N).val = H.val.map (stabilizerPointHom (ofJ0 K) g).toAddMonoidHom :=
  smul_addSubgroup_eq_map g H.val

theorem negation_cyclic_smul {N : ℕ} (H : CyclicSubgroup K N) :
    charTwoNegation (K := K) • H = H := by
  apply Subtype.ext
  rw [cyclic_smul_val]
  ext P
  change (∃ Q ∈ H.val, stabilizerPointEquiv (ofJ0 K) charTwoNegation.val
    (MulAction.mem_stabilizer_iff.mp charTwoNegation.property) Q = P) ↔ P ∈ H.val
  simp only [charTwoNegation_point]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact H.val.neg_mem hQ
  · intro hP
    exact ⟨-P, H.val.neg_mem hP, neg_neg P⟩

theorem sign_le_cyclic_action_kernel (N : ℕ) :
    charTwoSignSubgroup ≤ (MulAction.toPermHom
      (MulAction.stabilizer (VariableChange K) (ofJ0 K)) (CyclicSubgroup K N)).ker := by
  rw [charTwoSignSubgroup, Subgroup.zpowers_le, MonoidHom.mem_ker]
  apply Equiv.ext
  intro H
  exact negation_cyclic_smul H

variable [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal

/-- The actual order-twelve sign quotient acts on the same cyclic subgroups. -/
scoped instance cyclicSignAction (N : ℕ) :
    MulAction ((MulAction.stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup)
      (CyclicSubgroup K N) :=
  MulAction.compHom _ (QuotientGroup.lift charTwoSignSubgroup
    (MulAction.toPermHom _ (CyclicSubgroup K N)) (sign_le_cyclic_action_kernel N))

theorem signProjection_cyclic_smul {N : ℕ}
    (g : MulAction.stabilizer (VariableChange K) (ofJ0 K)) (H : CyclicSubgroup K N) :
    charTwoSignProjection g • H = g • H := by
  rw [MulAction.compHom_smul_def]
  rfl

end
end Dubon2026.SourceEllipticCharTwo
