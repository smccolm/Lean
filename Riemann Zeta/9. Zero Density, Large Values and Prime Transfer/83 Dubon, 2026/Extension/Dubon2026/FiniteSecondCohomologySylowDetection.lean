import Dubon2026.SubgroupCohomologyCoprimeDetection
import Dubon2026.ContinuousFiniteH2CardAnnihilation

/-! # Actual finite second cohomology is detected on original Sylow coefficients -/

namespace Dubon2026
noncomputable section

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep k G)

/-- The already proved undivided original cocycle sum annihilates actual
algebraic second cohomology by the original group order. -/
theorem finiteSecondCohomology_card_nsmul_eq_zero
    (x : groupCohomology A 2) : Fintype.card G • x = 0 := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [← map_nsmul]
    apply (groupCohomology.H2π_eq_zero_iff _).mpr
    exact ⟨fun g => ∑ t, c (g, t), finiteTwoCocycle_sum_boundary A c⟩

/-- If every genuine Sylow subgroup comparison kills an original second
cohomology class, that same class is zero. The proof uses the actual index
annihilation and the original finite group order, with no finiteness premise
on the full second cohomology group. -/
theorem finiteSecondCohomology_sylow_zero
    (x : groupCohomology A 2)
    (hx : ∀ p : ℕ, p.Prime → p ∣ Fintype.card G → ∃ P : Sylow p G,
      subgroupCohomologyComparison A (P : Subgroup G) 2 x = 0) : x = 0 := by
  have hord : addOrderOf x ∣ Fintype.card G :=
    addOrderOf_dvd_of_nsmul_eq_zero (finiteSecondCohomology_card_nsmul_eq_zero A x)
  have hone : addOrderOf x = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := hx p hp (hpd.trans hord)
    letI : Fintype (G ⧸ (P : Subgroup G)) := Fintype.ofFinite _
    have hi := subgroupCohomologyComparison_kernel_annihilated A
      (P : Subgroup G) 2 x hP
    have hd := hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hi)
    apply P.not_dvd_index
    simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

end
end Dubon2026
