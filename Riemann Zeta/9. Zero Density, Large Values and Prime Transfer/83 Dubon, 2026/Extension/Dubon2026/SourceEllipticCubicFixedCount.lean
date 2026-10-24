import Dubon2026.SourceEllipticCubicNonscalar
import Dubon2026.SourceEllipticCubicAction
import Dubon2026.SourceEllipticFixedCoordinateSubgroups
import Dubon2026.SourceEllipticQuadraticFixedCounts

/-! DUB-17/18 -> reverse genus -> exceptional j=0 fiber census.
The actual cubic coordinate automorphism has exactly nuThree(N) fixed
cyclic subgroups. Its quadratic identity and non-scalar prime-torsion
action are proved, and the existing torsion theorem supplies its basis.
The full stabilizer-orbit and modular-place counts remain required. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer SourceLevelProjective SourceQuadraticCyclicCount
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L]

theorem cubic_fixed_cyclic_count
    (B : L) (hB : B ≠ 0) (u : Lˣ) (hu : (u : L) ^ 3 = 1) (hu1 : (u : L) ≠ 1)
    (h2 : (2 : L) ≠ 0) (N : ℕ) (hN : (N : L) ≠ 0) :
    Nat.card {H : AddSubgroup (EB B).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N ∧
      ∀ P ∈ H, ∃ Q ∈ H,
        HEq (vcInvFun (⟨u, 0, 0, 0⟩ : VariableChange L) (EB B).toAffine P) Q}
      = nuThree N := by
  have hN0 : N ≠ 0 := fun h => hN (by simp [h])
  have h3 : (3 : L) ≠ 0 := by
    intro h3
    apply hu1
    have hz : ((u : L) - 1) ^ 3 = 0 := by
      linear_combination hu + ((u : L) - (u : L) ^ 2) * h3
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hz)
  haveI : (EB B).IsElliptic := isElliptic_EB B hB h2 h3
  let σ := (stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩
    (cubic_change_fixes u hu B)).toAddMonoidHom
  have hσ : ∀ P, σ (σ P) + σ P + P = 0 := cubic_action_relation B hB u hu hu1 h2
  have hns : ∀ p : ℕ, p.Prime → p ∣ N →
      ∃ P : (EB B).toAffine.Point, addOrderOf P = p ∧ ∀ k : ℕ, σ P ≠ k • P := by
    intro p hp hpN
    have hpL : (p : L) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hpN
      intro he
      apply hN
      push_cast
      rw [he, zero_mul]
    exact cubic_exists_order_prime_nonscalar B hB u hu1 h2 h3 σ
      (cubic_action_x B u hu) hσ p hp hpL
  rw [← elliptic_stable_cyclic_card_eq_nuThree (EB B) N hN σ hσ hns]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun H => ?_
  refine and_congr_right fun _hc => and_congr_right fun hcard => ?_
  haveI : Finite H := Nat.finite_of_card_ne_zero (hcard.trans_ne hN0)
  exact fixed_coordinate_iff_map_eq (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B) H

end
end Dubon2026.SourceEllipticExceptional
