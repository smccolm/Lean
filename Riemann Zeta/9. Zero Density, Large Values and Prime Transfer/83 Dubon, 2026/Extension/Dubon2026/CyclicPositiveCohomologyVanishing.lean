import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Actual positive cyclic cohomology from norm and first cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include g hg in
/-- The periodic cochain resolution identifies every positive even cyclic
cohomology class with an original invariant modulo the literal norm image. -/
theorem cyclic_evenCohomology_zero_of_norm_preimages
    (hnorm : ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x)
    (n : ℕ) [NeZero n] (hn : Even n) : Limits.IsZero (groupCohomology A n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg n hn
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance x
  apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg n hn y).mpr
  have hy : A.ρ g y.val = y.val := by
    have h := y.property
    change A.ρ g y.val - y.val = 0 at h
    exact sub_eq_zero.mp h
  exact hnorm y.val
    ((Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g hg y.val).mpr hy)

include g hg in
/-- The same periodic resolution transports vanishing of actual first
cohomology to all odd degrees. -/
theorem cyclic_oddCohomology_zero_of_first
    (hfirst : Limits.IsZero (groupCohomology A 1)) (n : ℕ) (hn : Odd n) :
    Limits.IsZero (groupCohomology A n) := by
  exact hfirst.of_iso
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg n hn ≪≫
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide)).symm)

include g hg in
/-- Actual invariant norm preimages and vanishing first cohomology exhaust
the two parities of the original positive cyclic cochain complex. -/
theorem cyclic_positiveCohomology_zero
    (hnorm : ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x)
    (hfirst : Limits.IsZero (groupCohomology A 1)) (n : ℕ) (hn : 0 < n) :
    Limits.IsZero (groupCohomology A n) := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rcases Nat.even_or_odd n with he | ho
  · exact cyclic_evenCohomology_zero_of_norm_preimages A g hg hnorm n he
  · exact cyclic_oddCohomology_zero_of_first A g hg hfirst n ho

end
end Dubon2026
