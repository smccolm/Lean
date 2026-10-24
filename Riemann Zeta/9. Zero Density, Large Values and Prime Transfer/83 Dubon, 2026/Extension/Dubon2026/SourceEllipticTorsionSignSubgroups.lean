import Dubon2026.SourceEllipticGaloisTorsionMap
import Dubon2026.SourceCyclicTorsionTransport

/-! Identity or negation on the actual N-torsion fixes every subgroup
of order N. The native element-order divisibility theorem supplies the
torsion-membership premise. This is the DUB-17/18 inertia-kernel bridge
from points to the original modular-field embedding correspondence. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
variable {B M : Type*} [Field B] [Field M] [Algebra B M] [DecidableEq M]

theorem subgroup_map_eq_of_torsion_sign
    (E : WeierstrassCurve B) (N : ℕ) (σ : M ≃ₐ[B] M)
    (hσ : (∀ P, galoisTorsionMap E N σ P = P) ∨
      (∀ P, galoisTorsionMap E N σ P = -P))
    (S : AddSubgroup (E.baseChange M).toAffine.Point) (hS : Nat.card S = N) :
    S.map (Point.map (W' := E) σ.toAlgHom) = S := by
  have htor (P : (E.baseChange M).toAffine.Point) (hP : P ∈ S) :
      P ∈ Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) := by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [← hS]
    exact AddSubgroup.addOrderOf_dvd_natCard S hP
  rcases hσ with hid | hneg
  · have hact (P : (E.baseChange M).toAffine.Point) (hP : P ∈ S) :
        Point.map (W' := E) σ.toAlgHom P = P :=
      congrArg Subtype.val (hid ⟨P, htor P hP⟩)
    ext Q
    constructor
    · rintro ⟨P, hP, rfl⟩
      rw [hact P hP]
      exact hP
    · intro hQ
      exact ⟨Q, hQ, hact Q hQ⟩
  · have hact (P : (E.baseChange M).toAffine.Point) (hP : P ∈ S) :
        Point.map (W' := E) σ.toAlgHom P = -P :=
      congrArg Subtype.val (hneg ⟨P, htor P hP⟩)
    ext Q
    constructor
    · rintro ⟨P, hP, rfl⟩
      rw [hact P hP]
      exact S.neg_mem hP
    · intro hQ
      refine ⟨-Q, S.neg_mem hQ, ?_⟩
      rw [hact (-Q) (S.neg_mem hQ), neg_neg]

end
end Dubon2026.SourceEllipticReduction
