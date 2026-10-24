import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-! Native group-index divisibility gives the orbit bound needed for the
DUB-17/18 wild normalized-order comparison. The kernel-fixes-point premise
is discharged by the actual normal-field inertia consumer.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three, natCard_orbit_dvd. -/
namespace Dubon2026.SourceCurve

theorem orbit_card_dvd_of_kernel_fixes {G X P : Type*} [Group G] [Group P] [MulAction G X]
    (π : G →* P) (x : X) (hker : ∀ g, π g = 1 → g • x = x) :
    Nat.card (MulAction.orbit G x) ∣ Nat.card P := by
  have hi : (MulAction.stabilizer G x).index = Nat.card (MulAction.orbit G x) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hle : π.ker ≤ MulAction.stabilizer G x := fun g hg => hker g hg
  have hd := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_ker, hi] at hd
  exact hd.trans (Subgroup.card_subgroup_dvd_card π.range)

end Dubon2026.SourceCurve
