import Dubon2026.SourceSanovFree
import Dubon2026.SourceSanovRange

/-! The actual level-four congruence subgroup supplies the free group needed by H2 vanishing.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective H1 coefficient maps -> Gamma0 H2 vanishing after
inverting six -> the actual free intersection with Gamma 4.

The integral-entry argument is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). Native Nielsen-Schreier and the literal
subgroup inclusion transfer the proved matrix-word freeness.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- Every actual matrix in Gamma 4 satisfies the original integral congruences
used by the proved free-word reduction. -/
theorem sourceGammaFour_sanovEntries {g : SL(2, ℤ)} (hg : g ∈ Gamma 4) :
    sourceSanovEntries g := by
  rw [Gamma_mem] at hg
  obtain ⟨ha, hb, hc, hd⟩ := hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : (4 : ℤ) ∣ g.val 0 0 - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by push_cast; simp [ha])
    omega
  · have h : (4 : ℤ) ∣ g.val 1 1 - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by push_cast; simp [hd])
    omega
  · exact dvd_trans (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hb)
  · exact dvd_trans (by norm_num) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hc)

/-- The actual level-four congruence group lies in the proved original free matrix subgroup. -/
theorem sourceGammaFour_le_sanov :
    Gamma 4 ≤ (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range :=
  fun g hg => sourceSanov_mem_range g (sourceGammaFour_sanovEntries hg)

/-- The original Gamma 4 subgroup is free, by the actual matrix inclusion
and native Nielsen-Schreier. -/
theorem sourceGammaFour_free : IsFreeGroup (Gamma 4) := by
  let S := (FreeGroup.lift ![sourceSanovA, sourceSanovB] : FreeGroup (Fin 2) →* SL(2, ℤ)).range
  letI : IsFreeGroup S := sourceSanov_range_free
  letI : IsFreeGroup ((Gamma 4).subgroupOf S) := subgroupIsFreeOfIsFree _
  exact IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe sourceGammaFour_le_sanov)

/-- The actual intersection of Gamma 4 with every original Gamma0 level
is a free group. No abstract freeness certificate is supplied. -/
theorem sourceGammaFour_subgroup_free (Q : ℕ) :
    IsFreeGroup ((Gamma 4).subgroupOf (Gamma0 Q)) := by
  letI : IsFreeGroup (Gamma 4) := sourceGammaFour_free
  let j : (Gamma 4).subgroupOf (Gamma0 Q) →* Gamma 4 :=
    { toFun := fun g => ⟨g.val.val, g.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b h
    have he : a.val.val = b.val.val := congrArg (fun g : Gamma 4 => g.val) h
    exact Subtype.ext (Subtype.ext he)
  letI : IsFreeGroup j.range := subgroupIsFreeOfIsFree _
  exact IsFreeGroup.ofMulEquiv (MonoidHom.ofInjective hj).symm

end
end Dubon2026
