import Dubon2026.PermutationOrbitCohomology

/-! # Original cohomology from the actual displayed permutation basis

Consume the original basis-coordinate isomorphism and the proved orbit
calculation. This is the required original-object cohomology consumer
for the constructed S-unit finite-index sublattice in DUB-17.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped Classical
attribute [local instance 1100] Rep.hV2
variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [Fintype ι] (A : Rep ℤ G) (b : Module.Basis ι ℤ A)
  (hb : ∀ g i, A.ρ g (b i) = b (g • i))
include hb

/-- The actual displayed permutation basis proves original H1/H2 finiteness, H1 order one, and the exact original orbit-stabilizer product for H2. -/
theorem permutedBasis_cohomology_orders :
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = 1 ∧
      Nat.card (groupCohomology A 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) := by
  let e (n : ℕ) : groupCohomology A n ≃ groupCohomology (permutationCoordinateRep ℤ G ι) n :=
    ((groupCohomology.functor ℤ G n).mapIso
    (permutationBasisCoordinateIso ℤ G ι A b hb)).toLinearEquiv.toEquiv
  letI : Subsingleton (groupCohomology (permutationCoordinateRep ℤ G ι) 1) :=
    ModuleCat.isZero_iff_subsingleton.mp (permutationCoordinate_first_cohomology_zero G ι)
  letI : Subsingleton (groupCohomology A 1) := Function.Injective.subsingleton (e 1).injective
  have h2 := permutationCoordinate_second_cohomology_order G ι
  letI := h2.1
  refine ⟨inferInstance,
    Finite.of_equiv (groupCohomology (permutationCoordinateRep ℤ G ι) 2) (e 2).symm,
    Nat.card_unique, ?_⟩
  exact (Nat.card_congr (e 2)).trans h2.2

end
end Dubon2026
