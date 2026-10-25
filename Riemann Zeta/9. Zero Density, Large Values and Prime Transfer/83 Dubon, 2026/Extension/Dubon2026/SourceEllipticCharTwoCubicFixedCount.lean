import Dubon2026.SourceEllipticCharTwoCubicPoint
import Dubon2026.SourceEllipticCharTwoCubicCommutator
import Dubon2026.SourceQuaternionCubicNonscalar
import Dubon2026.SourceEllipticQuadraticFixedCounts

/-! DUB-17/18 -> characteristic-two weighted exceptional census.
The actual cubic automorphism fixes exactly nuThree(N) cyclic subgroups.
The native addition law gives its quadratic identity; the actual stabilizer
commutator and proved torsion structure discharge nonscalar prime action. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer SourceEllipticExceptional
open SourceQuadraticCyclicCount SourceLevelProjective
noncomputable section
variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K] [IsAlgClosed K]

theorem char_two_cubic_fixed_cyclic_count (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    Nat.card {H : AddSubgroup (ofJ0 K).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N ∧ H.map (cubicPoint ω hω).toAddMonoidHom = H}
      = nuThree N := by
  letI : Fact (IsUnit (3 : K)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
  let φ := stabilizerPointHom (ofJ0 K)
  let α := φ (quarticStabilizer ω hω)
  let β := cubicPoint ω hω
  let δ := φ (cubicCommutator ω hω)
  have hδ : ∀ P, δ (δ P) = -P := by
    intro P
    have hm : δ * δ = φ charTwoNegation := by
      rw [← map_mul, cubicCommutator_square]
    change (δ * δ) P = -P
    rw [hm]
    exact charTwoNegation_point P
  have hcomp : ∀ P, δ P = β.symm (α (β (α.symm P))) := by
    have hm : δ = β⁻¹ * α * β * α⁻¹ := by
      change φ (cubicCommutator ω hω) = _
      rw [cubicCommutator, map_mul, map_mul, map_mul, map_inv, map_inv]
      rfl
    intro P
    rw [hm]
    rfl
  apply elliptic_stable_cyclic_card_eq_nuThree (ofJ0 K) N hNK β.toAddMonoidHom
    (cubicPoint_quadratic ω hω)
  intro p hp hpN
  have hpK : (p : K) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hpN
    intro h0
    apply hNK
    push_cast
    rw [h0, zero_mul]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpK (two_eq_zero K)
  obtain ⟨e⟩ : Nonempty (ZMod p × ZMod p ≃+
      Submodule.torsionBy ℤ (ofJ0 K).toAffine.Point p) := by
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self,
      WeierstrassCurve.map_id] using
      SourceEllipticTorsionStructure.actual_torsion_structure (ofJ0 K) hpK
  exact cubic_nonscalar_of_quaternion_commutator α β δ.toAddMonoidHom hδ hcomp p hp hp2 e

end
end Dubon2026.SourceEllipticCharTwo
