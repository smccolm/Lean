import Dubon2026.SourceEllipticStabilizerPointAction

/-! The literal fixed-subgroup condition in the exceptional-fiber source
is equality of subgroup images under the existing point equivalence.
Finite cardinality upgrades invariance by inclusion to equality. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticStabilizer
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

theorem fixed_coordinate_iff_map_eq (W : WeierstrassCurve L)
    (C : VariableChange L) (hC : C • W = W)
    (H : AddSubgroup W.toAffine.Point) [Finite H] :
    (∀ P ∈ H, ∃ Q ∈ H, HEq (vcInvFun C W.toAffine P) Q) ↔
      H.map (stabilizerPointEquiv W C hC).toAddMonoidHom = H := by
  constructor
  · intro h
    apply AddSubgroup.eq_of_le_of_card_ge
    · rintro _ ⟨P, hP, rfl⟩
      obtain ⟨Q, hQ, he⟩ := h P hP
      change stabilizerPointEquiv W C hC P ∈ H
      rwa [(stabilizerPointEquiv_eq_iff_heq W C hC P Q).mpr he]
    · rw [AddSubgroup.card_map_of_injective (stabilizerPointEquiv W C hC).injective]
  · intro h P hP
    refine ⟨stabilizerPointEquiv W C hC P, ?_,
      (stabilizerPointEquiv_eq_iff_heq W C hC P _).mp rfl⟩
    rw [← h]
    exact AddSubgroup.mem_map_of_mem _ hP

end
end Dubon2026.SourceEllipticExceptional
