import Dubon2026.SubgroupCohomologyCoprimeDetection

/-! # Actual cohomology detection on Sylow subgroups

DUB-17's finite relation duality needs the two low cohomology degrees of
the original lattice internal Hom. The existing comparison-trace identity
detects zero in either degree from actual Sylow restrictions, so no new
finite-group projectivity theorem or Tate complex is needed.
-/
namespace Dubon2026
noncomputable section

/-- Vanishing of an actual class on one Sylow subgroup for every prime
forces that class to vanish. The proof uses the original trace identity. -/
theorem finiteCohomology_sylow_zero
    {k G : Type} [CommRing k] [Group G] [Finite G]
    (A : Rep k G) (n : ℕ) (x : groupCohomology A n)
    (hx : ∀ p : ℕ, p.Prime → ∃ P : Sylow p G,
      subgroupCohomologyComparison A (P : Subgroup G) n x = 0) : x = 0 := by
  have hone : addOrderOf x = 1 := by
    by_contra hn
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, hP⟩ := hx p hp
    letI : Fintype (G ⧸ (P : Subgroup G)) := Fintype.ofFinite _
    have hi := subgroupCohomologyComparison_kernel_annihilated A
      (P : Subgroup G) n x hP
    have hd := hpd.trans (addOrderOf_dvd_of_nsmul_eq_zero hi)
    apply P.not_dvd_index
    simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

end
end Dubon2026
