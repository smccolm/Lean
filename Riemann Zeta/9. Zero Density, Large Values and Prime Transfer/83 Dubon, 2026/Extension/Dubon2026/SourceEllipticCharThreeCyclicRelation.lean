import Dubon2026.SourceEllipticCharThreeSixRealization
import Dubon2026.SourceEllipticCyclicStabilizerRelation
import Dubon2026.SourceCyclicSubgroupPermutation

/-! The literal full stabilizer relation is exactly the six-action
relation on the actual cyclic subgroups. This is the missing relational
input to the DUB-17/18 weighted characteristic-three place census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [CharP K 3]

theorem char_three_cyclic_stabilizer_related_iff_six (N : ℕ) (hN : N ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (S T : {S : AddSubgroup (EA (-1 : K)).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    let a := cyclicSubgroupEquiv N (stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩
      (quartic_change_fixes u hu (-1)))
    let b := cyclicSubgroupEquiv N (charThreeTranslation (K := K))
    cyclicStabilizerRelated (EA (-1 : K)) S.val T.val ↔
      (T = S ∨ T = a S ∨ T = b S ∨ T = b (b S) ∨ T = a (b S) ∨ T = a (b (b S))) := by
  dsimp only
  rw [cyclicStabilizerRelated_iff_map_eq _ N hN S T]
  simp only [Subtype.ext_iff]
  constructor
  · rintro ⟨γ, hγ, hST⟩
    have h := char_three_stabilizer_subgroup_six u hu γ hγ S.val
    dsimp only at h
    rw [hST] at h
    exact h
  · intro h
    exact char_three_six_subgroup_maps_realized u hu S.val T.val h

end
end Dubon2026.SourceEllipticExceptional
