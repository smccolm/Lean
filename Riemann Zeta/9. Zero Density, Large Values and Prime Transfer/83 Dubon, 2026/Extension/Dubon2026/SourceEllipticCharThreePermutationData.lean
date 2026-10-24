import Dubon2026.SourceEllipticCharThreeCyclicRelation
import Dubon2026.SourceEllipticCharThreeCubicFixedCount
import Dubon2026.SourceEllipticExceptionalOrbitCounts

/-! All relations and fixed-point counts for the actual characteristic-
three cyclic-subgroup permutations. These discharge the permutation
inputs to the DUB-17/18 weighted modular place census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer SourceLevelProjective
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] [CharP K 3]

theorem char_three_cyclic_permutation_data (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 2 = -1) :
    let a := cyclicSubgroupEquiv N (stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩
      (quartic_change_fixes u hu (-1)))
    let b := cyclicSubgroupEquiv N (charThreeTranslation (K := K))
    (∀ H, a (a H) = H) ∧ (∀ H, b (b (b H)) = H) ∧
      (∀ H, a (b H) = b (b (a H))) ∧
      Nat.card {H // a H = H} = nuTwo N ∧ Nat.card {H // b H = H} = nuThree N := by
  let α := stabilizerPointEquiv (EA (-1 : K)) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu (-1))
  let β := charThreeTranslation (K := K)
  let a := cyclicSubgroupEquiv N α
  let b := cyclicSubgroupEquiv N β
  have ha : a ^ 2 = 1 := cyclicSubgroupEquiv_square N α (quartic_action_square (-1) u hu)
  have hb : b ^ 3 = 1 := cyclicSubgroupEquiv_cube N β charThreeTranslation_quadratic
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro H
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
      congrArg (fun e => e H) ha
  · intro H
    simpa only [pow_succ, pow_two, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
      congrArg (fun e => e H) hb
  · intro H
    apply Subtype.ext
    change (H.val.map β.toAddMonoidHom).map α.toAddMonoidHom =
      ((H.val.map α.toAddMonoidHom).map β.toAddMonoidHom).map β.toAddMonoidHom
    simp only [AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext (charThreeTranslation_conjugation u hu)
  · rw [cyclic_stabilizer_fixed_card N (NeZero.ne N)]
    exact quartic_fixed_cyclic_count (-1 : K) (by simp) u hu
      two_ne_zero_of_char_three N hNK
  · rw [cyclicSubgroupEquiv_fixed_card]
    exact char_three_translation_fixed_cyclic_count N hNK

end
end Dubon2026.SourceEllipticExceptional
