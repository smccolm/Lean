import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! The actual level-four intersection has index dividing 48.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective H1 coefficient maps -> Gamma0 H2 vanishing after
inverting six -> invertible actual free-subgroup index.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). The finite matrix count is checked by the
kernel on the actual SL2 group over ZMod 4.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- The actual index of Gamma 4 inside Gamma0 Q divides its ambient index. -/
theorem sourceGammaFour_subgroup_index_dvd (Q : ℕ) :
    ((Gamma 4).subgroupOf (Gamma0 Q)).index ∣ (Gamma 4).index := by
  letI : (Gamma 4).Normal := Gamma_normal 4
  exact Subgroup.relIndex_dvd_index_of_normal (H := Gamma 4) (K := Gamma0 Q)

/-- The ambient congruence index divides the order of the actual finite matrix group. -/
theorem sourceGammaFour_index_dvd_card :
    (Gamma 4).index ∣ Nat.card (SL(2, ZMod 4)) := by
  have he : (Gamma 4).index = Nat.card
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 4))).range :=
    Subgroup.index_ker _
  rw [he]
  exact Subgroup.card_subgroup_dvd_card _

/-- The actual determinant-one matrix group over ZMod 4 has 48 elements. -/
theorem sourceSL2ZModFour_card : Nat.card (SL(2, ZMod 4)) = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The actual free congruence intersection at every original level has index dividing 48. -/
theorem sourceGammaFour_subgroup_index_dvd_48 (Q : ℕ) :
    ((Gamma 4).subgroupOf (Gamma0 Q)).index ∣ 48 :=
  (sourceGammaFour_subgroup_index_dvd Q).trans
    (sourceGammaFour_index_dvd_card.trans (dvd_of_eq sourceSL2ZModFour_card))

end
end Dubon2026
