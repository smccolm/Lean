import Dubon2026.SourceEllipticCharTwoCyclicAction

/-! DUB-17/18 -> weighted exceptional census. The actual sign-quotient
orbits are exactly the stabilizer relation already used by the modular-place
classifier, and its fixed points are the subgroup images already counted. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer SourceLevelProjective MulAction
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2]
attribute [local instance] charTwoSignSubgroup_normal

theorem cyclic_sign_orbit_eq {N : ℕ} (H : CyclicSubgroup K N) :
    orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H =
      orbit (stabilizer (VariableChange K) (ofJ0 K)) H := by
  ext T
  constructor
  · rintro ⟨g, rfl⟩
    induction g using QuotientGroup.induction_on with
    | H g => exact ⟨g, (signProjection_cyclic_smul g H).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨charTwoSignProjection g, signProjection_cyclic_smul g H⟩

theorem cyclicStabilizerRelated_iff_sign_orbit {N : ℕ} (hN : N ≠ 0)
    (H T : CyclicSubgroup K N) :
    cyclicStabilizerRelated (ofJ0 K) H.val T.val ↔
      T ∈ orbit ((stabilizer (VariableChange K) (ofJ0 K)) ⧸ charTwoSignSubgroup) H := by
  rw [cyclic_sign_orbit_eq, cyclicStabilizerRelated_iff_map_eq _ N hN]
  constructor
  · rintro ⟨C, hC, he⟩
    refine ⟨⟨C, mem_stabilizer_iff.mpr hC⟩, Subtype.ext ?_⟩
    rw [cyclic_smul_val]
    exact he
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, mem_stabilizer_iff.mp g.property, (cyclic_smul_val g H).symm⟩

theorem fixed_cyclic_action_card {N : ℕ}
    (g : stabilizer (VariableChange K) (ofJ0 K)) :
    Nat.card (fixedBy (CyclicSubgroup K N) (charTwoSignProjection g)) =
      Nat.card {H : AddSubgroup (ofJ0 K).toAffine.Point //
        IsAddCyclic H ∧ Nat.card H = N ∧ H.map (stabilizerPointHom (ofJ0 K) g).toAddMonoidHom = H} := by
  refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter
      (fun H : AddSubgroup (ofJ0 K).toAffine.Point => IsAddCyclic H ∧ Nat.card H = N)
      (fun H : AddSubgroup (ofJ0 K).toAffine.Point =>
        H.map (stabilizerPointHom (ofJ0 K) g).toAddMonoidHom = H)).trans
      (Equiv.subtypeEquivRight fun _ => and_assoc)))
  intro H
  rw [mem_fixedBy, signProjection_cyclic_smul, Subtype.ext_iff, cyclic_smul_val]

theorem char_two_cyclic_action_fixed_counts [IsAlgClosed K]
    (ω : K) (hω : ω ^ 2 + ω + 1 = 0) (N : ℕ) (hNK : (N : K) ≠ 0) :
    Nat.card (fixedBy (CyclicSubgroup K N) (charTwoSignProjection (quarticStabilizer ω hω))) = nuTwo N ∧
    Nat.card (fixedBy (CyclicSubgroup K N) (charTwoSignProjection (cubicStabilizer ω hω))) = nuThree N := by
  rw [fixed_cyclic_action_card, fixed_cyclic_action_card]
  exact ⟨char_two_quartic_fixed_cyclic_count ω hω N hNK,
    char_two_cubic_fixed_cyclic_count ω hω N hNK⟩

end
end Dubon2026.SourceEllipticCharTwo
