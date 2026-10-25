import Dubon2026.SourceEllipticCharTwoQuaternionStabilizers
import Dubon2026.SourceQuaternionQuarticNonscalar
import Dubon2026.SourceEllipticQuadraticFixedCounts

/-! DUB-17/18 -> characteristic-two weighted exceptional census.
The actual quartic automorphism fixes exactly nuTwo(N) cyclic subgroups.
Its quaternion relations and nonscalar prime-torsion action are derived
from explicit stabilizer elements and the existing actual torsion structure. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve SourceEllipticStabilizer SourceEllipticExceptional
open SourceQuadraticCyclicCount SourceLevelProjective
noncomputable section
variable {K : Type*} [Field K] [CharP K 2] [DecidableEq K] [IsAlgClosed K]

theorem char_two_quartic_fixed_cyclic_count (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
    (N : ℕ) (hNK : (N : K) ≠ 0) :
    Nat.card {H : AddSubgroup (ofJ0 K).toAffine.Point //
      IsAddCyclic H ∧ Nat.card H = N ∧
        H.map (stabilizerPointHom (ofJ0 K) (quarticStabilizer ω hω)).toAddMonoidHom = H}
      = nuTwo N := by
  letI : Fact (IsUnit (3 : K)) := ⟨by rw [three_eq_one]; exact isUnit_one⟩
  let φ := stabilizerPointHom (ofJ0 K)
  let α := φ (quarticStabilizer ω hω)
  let β := φ (cubicStabilizer ω hω)
  let δ := φ (quaternionStabilizer ω hω)
  have hα : ∀ P, α (α P) = -P := by
    intro P
    have hm : α * α = φ charTwoNegation := by
      rw [← map_mul, quarticStabilizer_square]
    change (α * α) P = -P
    rw [hm]
    exact charTwoNegation_point P
  have hδ : ∀ P, δ (δ P) = -P := by
    intro P
    have hm : δ * δ = φ charTwoNegation := by
      rw [← map_mul, quaternionStabilizer_square]
    change (δ * δ) P = -P
    rw [hm]
    exact charTwoNegation_point P
  have hcomp : ∀ P, δ P = α (β (α (β.symm P))) := by
    have hm : δ = α * (β * α * β⁻¹) := by
      change φ (quaternionStabilizer ω hω) = _
      rw [quaternionStabilizer_eq, map_mul, map_mul, map_mul, map_inv]
    intro P
    rw [hm]
    rfl
  apply elliptic_stable_cyclic_card_eq_nuTwo (ofJ0 K) N hNK α.toAddMonoidHom hα
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
  exact quartic_nonscalar_of_quaternion_relations α.toAddMonoidHom β δ.toAddMonoidHom
    hα hδ hcomp p hp hp2 e

end
end Dubon2026.SourceEllipticCharTwo
