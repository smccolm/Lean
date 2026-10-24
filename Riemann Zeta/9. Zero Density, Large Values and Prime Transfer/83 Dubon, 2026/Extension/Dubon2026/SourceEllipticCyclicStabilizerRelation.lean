import Dubon2026.SourceEllipticStabilizerPointAction
import Dubon2026.SourceEllipticCyclicCount

/-! The exact source equivalence relation on cyclic subgroups is an image
equality under the actual stabilizing coordinate change. Finite cardinality
upgrades the source inclusion to equality. This is required to transfer
the full inertia image up to sign to the exceptional-fiber orbit count. -/
namespace Dubon2026.SourceEllipticStabilizer
open WeierstrassCurve SourceEllipticVariableChange
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

/-- The literal coordinate-change relation in the source exceptional-fiber theorem. -/
def cyclicStabilizerRelated (W : WeierstrassCurve K)
    (S T : AddSubgroup W.toAffine.Point) : Prop :=
  ∃ C : VariableChange K, C • W = W ∧
    ∀ P ∈ S, ∃ Q ∈ T, HEq (vcInvFun C W.toAffine P) Q

theorem cyclicStabilizerRelated_iff_map_le (W : WeierstrassCurve K)
    (S T : AddSubgroup W.toAffine.Point) :
    cyclicStabilizerRelated W S T ↔
      ∃ (C : VariableChange K) (hC : C • W = W),
        S.map (stabilizerPointEquiv W C hC).toAddMonoidHom ≤ T := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨Q, hQ, hPQ⟩ := h P hP
    change stabilizerPointEquiv W C hC P ∈ T
    rwa [(stabilizerPointEquiv_eq_iff_heq W C hC P Q).mpr hPQ]
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun P hP => ?_⟩
    exact ⟨_, h (AddSubgroup.mem_map_of_mem _ hP),
      (stabilizerPointEquiv_eq_iff_heq W C hC P _).mp rfl⟩

theorem cyclicStabilizerRelated_iff_map_eq (W : WeierstrassCurve K)
    (N : ℕ) (hN : N ≠ 0)
    (S T : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    cyclicStabilizerRelated W S.val T.val ↔
      ∃ (C : VariableChange K) (hC : C • W = W),
        S.val.map (stabilizerPointEquiv W C hC).toAddMonoidHom = T.val := by
  rw [cyclicStabilizerRelated_iff_map_le]
  refine exists_congr fun C => exists_congr fun hC => ?_
  constructor
  · intro hle
    haveI : Finite T.val := Nat.finite_of_card_ne_zero (by rwa [T.property.2])
    apply AddSubgroup.eq_of_le_of_card_ge hle
    rw [AddSubgroup.card_map_of_injective (stabilizerPointEquiv W C hC).injective,
      S.property.2, T.property.2]
  · exact fun h => h.le

end
end Dubon2026.SourceEllipticStabilizer
