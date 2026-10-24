import Dubon2026.SourceEllipticQuarticFixedCount
import Dubon2026.SourceEllipticCubicFixedCount
import Dubon2026.SourceCyclicSubgroupPermutation
import Dubon2026.SourceEllipticCyclicCount
import Dubon2026.SourceLevelPsiPrimeStep
import Dubon2026.SourceManinOrbitCount

/-! DUB-17/18 -> exceptional place census. The existing two- and
three-cycle orbit counts combine the actual fixed-subgroup census with
the proved Dedekind-psi count of all elliptic cyclic subgroups. The full
coordinate-change relation must still be identified with these orbits
before composing with the original modular-place classifier. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticStabilizer
open SourceLevelProjective SourceManin
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem cyclic_stabilizer_fixed_card (N : ℕ) (hN : N ≠ 0)
    (W : WeierstrassCurve K) (C : VariableChange K) (hC : C • W = W) :
    Nat.card {H // cyclicSubgroupEquiv N (stabilizerPointEquiv W C hC) H = H} =
      Nat.card {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N ∧
        ∀ P ∈ H, ∃ Q ∈ H, HEq (vcInvFun C W.toAffine P) Q} := by
  rw [cyclicSubgroupEquiv_fixed_card]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun H => ?_
  refine and_congr_right fun _hc => and_congr_right fun hcard => ?_
  haveI : Finite H := Nat.finite_of_card_ne_zero (hcard.trans_ne hN)
  exact (fixed_coordinate_iff_map_eq W C hC H).symm

theorem quartic_cyclic_orbit_count [IsAlgClosed K]
    (A : K) (hA : A ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (h2 : (2 : K) ≠ 0) (N : ℕ) (hN : (N : K) ≠ 0) :
    2 * Nat.card (Orb (cyclicSubgroupEquiv N
      (stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A)))) =
      dedekindPsi N + nuTwo N := by
  have hN0 : N ≠ 0 := fun h => hN (by simp [h])
  haveI : (EA A).IsElliptic := isElliptic_EA A hA h2
  have hc : Nat.card {H : AddSubgroup (EA A).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N} = dedekindPsi N := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (EA A) hN
  haveI : Finite {H : AddSubgroup (EA A).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N} :=
    Nat.finite_of_card_ne_zero (hc.trans_ne (dedekindPsi_pos hN0).ne')
  rw [two_mul_natCard_orb _ (cyclicSubgroupEquiv_square N _ (quartic_action_square A u hu)),
    hc, cyclic_stabilizer_fixed_card N hN0,
    quartic_fixed_cyclic_count A hA u hu h2 N hN]

theorem cubic_cyclic_orbit_count [IsAlgClosed K]
    (B : K) (hB : B ≠ 0) (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)
    (h2 : (2 : K) ≠ 0) (N : ℕ) (hN : (N : K) ≠ 0) :
    3 * Nat.card (Orb (cyclicSubgroupEquiv N
      (stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B)))) =
      dedekindPsi N + 2 * nuThree N := by
  have hN0 : N ≠ 0 := fun h => hN (by simp [h])
  have h3 : (3 : K) ≠ 0 := by
    intro h3
    apply hu1
    have hz : ((u : K) - 1) ^ 3 = 0 := by
      linear_combination hu + ((u : K) - (u : K) ^ 2) * h3
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hz)
  haveI : (EB B).IsElliptic := isElliptic_EB B hB h2 h3
  have hc : Nat.card {H : AddSubgroup (EB B).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N} = dedekindPsi N := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality (EB B) hN
  haveI : Finite {H : AddSubgroup (EB B).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N} :=
    Nat.finite_of_card_ne_zero (hc.trans_ne (dedekindPsi_pos hN0).ne')
  rw [three_mul_natCard_orb _
      (cyclicSubgroupEquiv_cube N _ (cubic_action_relation B hB u hu hu1 h2)),
    hc, cyclic_stabilizer_fixed_card N hN0,
    cubic_fixed_cyclic_count B hB u hu hu1 h2 N hN]

end
end Dubon2026.SourceEllipticExceptional
