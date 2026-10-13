import Dubon2026.SubgroupCohomologyCoprimeDetection

/-! # Original first cohomology is detected on actual Sylow subgroups

The already proved comparison-trace identity, applied to the trivial
subgroup, gives degree annihilation. The same identity for Sylow subgroups
then detects zero. This is the final finite-group deduction needed to
remove the cyclic hypothesis from original idele-class H1 in DUB-17's
global invariant and duality dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- The actual finite group order annihilates original first cohomology. -/
theorem finiteFirstCohomology_card_nsmul_eq_zero
    (x : groupCohomology A 1) : Fintype.card G • x = 0 := by
  let S : Subgroup G := ⊥
  letI : Fintype (G ⧸ S) := Fintype.ofFinite _
  have hzero := isZero_groupCohomology_succ_of_subsingleton (Rep.res S.subtype A) 0
  haveI : Subsingleton (groupCohomology (Rep.res S.subtype A) 1) :=
    ModuleCat.isZero_iff_subsingleton.mp hzero
  have h := subgroupCohomologyComparison_kernel_annihilated A S 1 x
    (Subsingleton.elim _ _)
  rw [← Nat.card_eq_fintype_card] at h
  change S.index • x = 0 at h
  simpa only [S, Subgroup.index_bot, Nat.card_eq_fintype_card] using h

/-- Vanishing on actual Sylow comparisons forces an original H1 class to vanish. -/
theorem finiteFirstCohomology_sylow_zero
    (x : groupCohomology A 1)
    (hx : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Sylow p G,
      subgroupCohomologyComparison A (P : Subgroup G) 1 x = 0) : x = 0 := by
  have hord : addOrderOf x ∣ Fintype.card G :=
    addOrderOf_dvd_of_nsmul_eq_zero (finiteFirstCohomology_card_nsmul_eq_zero A x)
  have hone : addOrderOf x = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := hx p hp (hpd.trans hord)
    letI : Fintype (G ⧸ (P : Subgroup G)) := Fintype.ofFinite _
    have hi := subgroupCohomologyComparison_kernel_annihilated A
      (P : Subgroup G) 1 x hP
    have hd := hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hi)
    apply P.not_dvd_index
    simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

end
end Dubon2026
