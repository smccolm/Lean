import Dubon2026.CosetTransitionCoordinates

/-! # Actual subgroup coordinates for the continuous Shapiro homotopies

The existing original subgroup remainder supplies a left-equivariant coordinate.
Its continuity follows from the original open cosets. These are the precise
coordinates used to compare the two continuous Shapiro composites in DUB-17's
local duality dependency.
-/

namespace Dubon2026
noncomputable section

variable {G : Type} [Group G] (S : Subgroup G)

/-- The left-equivariant original subgroup coordinate, using the existing remainder. -/
def coinducedSubgroupCoordinate (g : G) : S := (subgroupCosetRemainder S g⁻¹)⁻¹

/-- The coordinate is exactly the original element times its inverse-coset representative. -/
theorem coinducedSubgroupCoordinate_val (g : G) :
    (coinducedSubgroupCoordinate S g : G) = g * subgroupCosetRepresentative S g⁻¹ := by
  change ((subgroupCosetRepresentative S g⁻¹)⁻¹ * g⁻¹)⁻¹ = _
  rw [mul_inv_rev, inv_inv, inv_inv]

/-- The same actual coordinate is equivariant under original left subgroup multiplication. -/
theorem coinducedSubgroupCoordinate_mul (s : S) (g : G) :
    coinducedSubgroupCoordinate S ((s : G) * g) = s * coinducedSubgroupCoordinate S g := by
  change (subgroupCosetRemainder S ((s : G) * g)⁻¹)⁻¹ = s * (subgroupCosetRemainder S g⁻¹)⁻¹
  rw [mul_inv_rev]
  change (subgroupCosetRemainder S (g⁻¹ * (s⁻¹ : S)))⁻¹ = _
  rw [subgroupCosetRemainder_mul, mul_inv_rev, inv_inv]

/-- On the original subgroup, the coordinate is right translation by its actual
identity value; no unproved normalization of the chosen representatives is used. -/
theorem coinducedSubgroupCoordinate_subgroup (s : S) :
    coinducedSubgroupCoordinate S (s : G) = s * coinducedSubgroupCoordinate S 1 := by
  simpa only [mul_one] using coinducedSubgroupCoordinate_mul S s 1

/-- The actual subgroup coordinate is continuous for the original open-subgroup topology. -/
theorem coinducedSubgroupCoordinate_continuous [TopologicalSpace G] [IsTopologicalGroup G]
    (hS : IsOpen (S : Set G)) : Continuous (coinducedSubgroupCoordinate S) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  have ht : Continuous (fun g : G => g * subgroupCosetRepresentative S g⁻¹) :=
    continuous_id.mul (hout.comp (QuotientGroup.continuous_mk.comp continuous_inv))
  apply continuous_induced_rng.mpr
  change Continuous (fun g => (coinducedSubgroupCoordinate S g : G))
  simpa only [coinducedSubgroupCoordinate_val] using ht

end
end Dubon2026
