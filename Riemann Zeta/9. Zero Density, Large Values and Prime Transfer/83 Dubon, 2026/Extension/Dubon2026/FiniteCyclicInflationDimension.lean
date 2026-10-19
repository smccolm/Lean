import Dubon2026.FiniteCyclicNormZero
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Finite cyclic inflation dimensions for DUB-17's unramified local
condition. The exact inflation map is the pinned H1 inflation-restriction
map. The proof route was checked against the reviewed public cyclic/depth
argument, but uses native objects and does not import its local-class model.
Original continuous comparison and arithmetic depth remain separate. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K G : Type} [Field K] [Group G] (A : Rep K G)
  (N : Subgroup G) [N.Normal]

/-- Taking invariants after passing to quotient invariants retains exactly
the original globally invariant vectors. -/
def quotientInvariantInvariantEquiv :
    (A.quotientToInvariants N).ρ.invariants ≃ₗ[K] A.ρ.invariants where
  toFun x := ⟨x.val.val, fun g => congrArg Subtype.val (x.property (QuotientGroup.mk g))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨⟨y.val, fun n => y.property n.val⟩, fun q =>
    QuotientGroup.induction_on q fun g => Subtype.ext (y.property g)⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := rfl

/-- The literal image of first inflation has the dimension of the
original quotient-group H1, by the proved inflation injection. -/
theorem firstInflation_range_finrank :
    Module.finrank K (groupCohomology.H1InfRes A N).f.hom.range =
      Module.finrank K (groupCohomology (A.quotientToInvariants N) 1) :=
  LinearMap.finrank_range_of_inj
    ((ModuleCat.mono_iff_injective _).mp (inferInstance : Mono (groupCohomology.H1InfRes A N).f))

/-- A cyclic finite quotient bounds its original inflation image by the
original globally invariant coefficient space. -/
theorem finite_cyclic_firstInflation_finrank_le [FiniteDimensional K A]
    [Fintype (G ⧸ N)] (g : G ⧸ N) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Module.finrank K (groupCohomology.H1InfRes A N).f.hom.range ≤
      Module.finrank K A.ρ.invariants := by
  letI : IsCyclic (G ⧸ N) := ⟨⟨g, hg⟩⟩
  letI : CommGroup (G ⧸ N) := IsCyclic.commGroup
  letI : FiniteDimensional K (A.quotientToInvariants N) :=
    inferInstanceAs (FiniteDimensional K (Representation.invariants (A.ρ.comp N.subtype)))
  rw [firstInflation_range_finrank]
  have h := finite_cyclic_H1_finrank_le_invariants (A.quotientToInvariants N) g hg
  rwa [(quotientInvariantInvariantEquiv A N).finrank_eq] at h

/-- At a characteristic-divisible action-period depth the original
inflation image attains the full invariant dimension. -/
theorem finite_cyclic_firstInflation_finrank_eq [FiniteDimensional K A]
    [Fintype (G ⧸ N)] (p d : ℕ) [CharP K p]
    (g : G ⧸ N) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hperiod : (A.quotientToInvariants N).ρ g ^ d = 1)
    (hsize : p * d ∣ Fintype.card (G ⧸ N)) :
    Module.finrank K (groupCohomology.H1InfRes A N).f.hom.range =
      Module.finrank K A.ρ.invariants := by
  letI : IsCyclic (G ⧸ N) := ⟨⟨g, hg⟩⟩
  letI : CommGroup (G ⧸ N) := IsCyclic.commGroup
  letI : FiniteDimensional K (A.quotientToInvariants N) :=
    inferInstanceAs (FiniteDimensional K (Representation.invariants (A.ρ.comp N.subtype)))
  rw [firstInflation_range_finrank]
  have h := finite_cyclic_H1_finrank_eq_of_characteristic_period_dvd
    (A.quotientToInvariants N) p d g hg hperiod hsize
  rwa [(quotientInvariantInvariantEquiv A N).finrank_eq] at h

end
end Dubon2026
