import Dubon2026.SourceTorsionEquivQuadraticFixedCounts
import Dubon2026.SourceEllipticTorsionStructure

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census.
The existing actual elliptic torsion theorem supplies the rank-two basis
required by the fixed-subgroup counts. Only the specific automorphism
identity and non-scalar action on prime torsion remain as inputs. -/
namespace Dubon2026.SourceQuadraticCyclicCount
noncomputable section
open SourceLevelProjective
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem elliptic_stable_cyclic_card_eq_nuTwo
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) (hn : (n : K) ≠ 0)
    (σ : W.toAffine.Point →+ W.toAffine.Point)
    (hσ : ∀ P, σ (σ P) = -P)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ P : W.toAffine.Point, addOrderOf P = p ∧ ∀ k : ℕ, σ P ≠ k • P) :
    Nat.card {H : AddSubgroup W.toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H} = nuTwo n := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  obtain ⟨e⟩ : Nonempty (ZMod n × ZMod n ≃+
      Submodule.torsionBy ℤ W.toAffine.Point n) := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticTorsionStructure.actual_torsion_structure W hn
  exact stable_cyclic_card_of_torsion_equiv_eq_nuTwo n e σ hσ hns

theorem elliptic_stable_cyclic_card_eq_nuThree
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) (hn : (n : K) ≠ 0)
    (σ : W.toAffine.Point →+ W.toAffine.Point)
    (hσ : ∀ P, σ (σ P) + σ P + P = 0)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n →
      ∃ P : W.toAffine.Point, addOrderOf P = p ∧ ∀ k : ℕ, σ P ≠ k • P) :
    Nat.card {H : AddSubgroup W.toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H} = nuThree n := by
  haveI : NeZero n := ⟨fun h => hn (by simp [h])⟩
  obtain ⟨e⟩ : Nonempty (ZMod n × ZMod n ≃+
      Submodule.torsionBy ℤ W.toAffine.Point n) := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticTorsionStructure.actual_torsion_structure W hn
  exact stable_cyclic_card_of_torsion_equiv_eq_nuThree n e σ hσ hns

end
end Dubon2026.SourceQuadraticCyclicCount
