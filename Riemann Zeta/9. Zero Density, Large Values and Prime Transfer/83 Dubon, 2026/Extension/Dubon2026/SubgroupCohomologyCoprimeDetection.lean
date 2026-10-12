import Dubon2026.CoinducedCohomologyTrace
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Sylow

/-! # Genuine subgroup detection on original primary cohomology classes -/

namespace Dubon2026
noncomputable section

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- The actual subgroup comparison detects zero on classes killed by an
integer coprime to the original coset index. -/
theorem subgroupCohomologyComparison_coprime_zero [Fintype (G ⧸ S)]
    (n m : ℕ) (hm : m.Coprime (Fintype.card (G ⧸ S)))
    (x : groupCohomology A n) (hx : m • x = 0)
    (hres : subgroupCohomologyComparison A S n x = 0) : x = 0 := by
  have h := gcd_nsmul_eq_zero.mpr
    ⟨hx, subgroupCohomologyComparison_kernel_annihilated A S n x hres⟩
  simpa only [hm.gcd_eq_one, one_nsmul] using h

/-- The same genuine comparison is injective on the original primary
component when its prime is coprime to the subgroup index. -/
theorem subgroupCohomologyComparison_primary_injective [Fintype (G ⧸ S)]
    (n p : ℕ) (hp : p.Coprime (Fintype.card (G ⧸ S))) :
    Function.Injective (fun x : AddCommGroup.primaryComponent (groupCohomology A n) p =>
      subgroupCohomologyComparison A S n x.val) := by
  intro x y hxy
  dsimp only at hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem := (AddCommGroup.primaryComponent (groupCohomology A n) p).sub_mem x.property y.property
  obtain ⟨m, hm⟩ := AddCommGroup.mem_primaryComponent.mp hmem
  apply subgroupCohomologyComparison_coprime_zero A S n (p ^ m) (hp.pow_left m) (x.val - y.val) hm
  rw [map_sub, hxy, sub_self]

/-- Every original primary cohomology component injects into the actual
cohomology of a Sylow subgroup with the original restricted coefficients. -/
theorem sylowCohomologyComparison_primary_injective [Finite G]
    (n p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Function.Injective (fun x : AddCommGroup.primaryComponent (groupCohomology A n) p =>
      subgroupCohomologyComparison A (P : Subgroup G) n x.val) := by
  letI : Fintype (G ⧸ (P : Subgroup G)) := Fintype.ofFinite _
  apply subgroupCohomologyComparison_primary_injective A (P : Subgroup G) n p
  have hp := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index
  change p.Coprime (Fintype.card (G ⧸ (P : Subgroup G)))
  simpa only [Subgroup.index, Nat.card_eq_fintype_card] using hp

end
end Dubon2026
