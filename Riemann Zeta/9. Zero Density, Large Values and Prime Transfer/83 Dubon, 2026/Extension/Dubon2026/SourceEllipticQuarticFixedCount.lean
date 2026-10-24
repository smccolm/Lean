import Dubon2026.SourceEllipticQuarticNonscalar
import Dubon2026.SourceEllipticFixedCoordinateSubgroups
import Dubon2026.SourceEllipticQuadraticFixedCounts

/-! DUB-17/18 -> reverse genus -> exceptional j=1728 fiber census.
The actual quartic coordinate automorphism has exactly nuTwo(N) fixed
cyclic subgroups. Both its quadratic identity and its non-scalar action
on prime torsion are derived; no action or torsion-basis assumption remains.
The subsequent stabilizer-orbit and modular-place counts remain required. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer SourceLevelProjective SourceQuadraticCyclicCount
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]

theorem quartic_fixed_cyclic_count
    (A : L) (hA : A ≠ 0) (u : Lˣ) (hu : (u : L) ^ 2 = -1)
    (h2 : (2 : L) ≠ 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (EA A).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N ∧
      ∀ P ∈ H, ∃ Q ∈ H,
        HEq (vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L) (EA A).toAffine P) Q}
      = nuTwo N := by
  have hN0 : N ≠ 0 := fun h => hN (by simp [h])
  haveI : (EA A).IsElliptic := isElliptic_EA A hA h2
  let σ := (stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩
    (quartic_change_fixes u hu A)).toAddMonoidHom
  have hσ : ∀ P, σ (σ P) = -P := quartic_action_square A u hu
  have hns : ∀ p : ℕ, p.Prime → p ∣ N →
      ∃ P : (EA A).toAffine.Point, addOrderOf P = p ∧ ∀ k : ℕ, σ P ≠ k • P := by
    intro p hp hpN
    have hpL : (p : L) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hpN
      intro he
      apply hN
      push_cast
      rw [he, zero_mul]
    exact quartic_exists_order_prime_nonscalar A hA h2 σ
      (quartic_action_x A u hu) hσ p hp hpL
  rw [← elliptic_stable_cyclic_card_eq_nuTwo (EA A) N hN σ hσ hns]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun H => ?_
  refine and_congr_right fun _hc => and_congr_right fun hcard => ?_
  haveI : Finite H := Nat.finite_of_card_ne_zero (hcard.trans_ne hN0)
  exact fixed_coordinate_iff_map_eq (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A) H

end
end Dubon2026.SourceEllipticExceptional
