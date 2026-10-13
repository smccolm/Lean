import Dubon2026.CyclicCarryPartialCochain
import Dubon2026.CyclicTwoCocycleColumnDetection

/-! # Actual finite cyclic H2 classes equal their explicit original carry classes

An explicit partial-column coboundary compares the same original cocycle
with the carry of its actual invariant period. No finiteness of the
coefficient or norm quotient is used. This supplies the global cyclic
class comparison required by DUB-17's local character pairing and
principal-product route to arithmetic invariant sum-zero.
-/
namespace Dubon2026
noncomputable section
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)
  {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n))
  (g : G) (hχ : χ g = Multiplicative.ofAdd 1)

include hχ in
private theorem actualIndex_generates : ∀ x, x ∈ Subgroup.zpowers g := by
  intro x
  rw [← cyclicCarryIndex_pow χ g hχ x]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _

include hχ in
/-- The original period coefficient is invariant under the whole actual indexed cyclic group. -/
theorem cyclicCarryPeriod_invariant (c : groupCohomology.cocycles₂ A) :
    ∀ x, A.ρ x (representationCyclicTwoCochainPeriodSum A g n c) =
      representationCyclicTwoCochainPeriodSum A g n c := by
  apply (Representation.mem_invariants_iff_of_forall_mem_zpowers A.ρ g
    (actualIndex_generates χ g hχ) _).mpr
  exact representationCyclicTwoCocyclePeriodSum_fixed A g n (cyclicCarryIndex_period χ g hχ) c

include hχ in
/-- Every original cyclic two-cocycle has the same actual H2 class as the explicit carry of its original period. -/
theorem cyclicTwoCocycleH2_eq_carry_of_period (hn : 1 < n)
    (c : groupCohomology.cocycles₂ A) :
    groupCohomology.H2π A c =
      groupCohomology.H2π A
        (representationCarryCocycle A χ.toMonoidHom
          (representationCyclicTwoCochainPeriodSum A g n c)
          (cyclicCarryPeriod_invariant A χ g hχ c)) := by
  haveI : Finite G := Finite.of_equiv (Multiplicative (ZMod n)) χ.symm.toEquiv
  let b := cyclicCarryPartialCochain A χ g c
  let d : groupCohomology.cocycles₂ A :=
    ⟨groupCohomology.d₁₂ A b, groupCohomology.d₁₂_apply_mem_cocycles₂ b⟩
  have he : c + d = representationCarryCocycle A χ.toMonoidHom
      (representationCyclicTwoCochainPeriodSum A g n c)
      (cyclicCarryPeriod_invariant A χ g hχ c) := by
    apply cyclicTwoCocycle_eq_of_generator_column A g (actualIndex_generates χ g hχ)
    intro x
    exact cyclicCarryPartialCochain_column A χ g hχ hn c x
  have hd : groupCohomology.H2π A d = 0 :=
    (groupCohomology.H2π_eq_zero_iff d).mpr ⟨b, rfl⟩
  rw [← he, map_add, hd, add_zero]

end
end Dubon2026
