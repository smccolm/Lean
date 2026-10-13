import Dubon2026.PermutationOrbitDecomposition

/-! # Original finite cyclic permutation cohomology and orbit stabilizers

The actual orbit decomposition and existing Shapiro computations give
zero H1 and finite H2 with order the product of the actual stabilizer
orders. This removes the permutation-cohomology input to the S-unit
finite-index comparison serving DUB-17's global norm-index argument.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped Classical
variable (G ι : Type) [CommGroup G] [MulAction G ι]

/-- The actual chosen representative, as a point of its original orbit. -/
def permutationOrbitPoint (ω : MulAction.orbitRel.Quotient G ι) : ω.orbit :=
  ⟨ω.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' ω)⟩

/-- The stabilizer of the original point inside its orbit is the same actual subgroup as its ambient stabilizer. -/
theorem permutationOrbitPoint_stabilizer (ω : MulAction.orbitRel.Quotient G ι) :
    MulAction.stabilizer G (permutationOrbitPoint G ι ω) = MulAction.stabilizer G ω.out := by
  ext g
  change (g • permutationOrbitPoint G ι ω = permutationOrbitPoint G ι ω) ↔ g • ω.out = ω.out
  exact Subtype.ext_iff

/-- Original cohomology is isomorphic to the product of the original orbit cohomologies. -/
def permutationOrbitCohomologyIso (R : Type) [CommRing R] [Fintype ι] (n : ℕ) :
    groupCohomology (permutationCoordinateRep R G ι) n ≅
      ModuleCat.of R (∀ ω : MulAction.orbitRel.Quotient G ι,
        groupCohomology (permutationCoordinateRep R G ω.orbit) n) :=
  (groupCohomology.functor R G n).mapIso (permutationOrbitRepIso R G ι) ≪≫
    originalFinitePiCohomologyIso (fun ω : MulAction.orbitRel.Quotient G ι =>
      permutationCoordinateRep R G ω.orbit) n

variable [Fintype G] [IsCyclic G] [Fintype ι]

/-- Original H1 of every finite integral permutation representation is zero. -/
theorem permutationCoordinate_first_cohomology_zero :
    Limits.IsZero (groupCohomology (permutationCoordinateRep ℤ G ι) 1) := by
  letI (ω : MulAction.orbitRel.Quotient G ι) :
      Subsingleton (groupCohomology (permutationCoordinateRep ℤ G ω.orbit) 1) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (transitivePermutation_first_cohomology_zero G ω.orbit (permutationOrbitPoint G ι ω))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact Function.Injective.subsingleton
    (permutationOrbitCohomologyIso G ι ℤ 1).toLinearEquiv.injective

/-- Original H2 of a finite integral permutation representation has exactly the product of its actual orbit-stabilizer orders. -/
theorem permutationCoordinate_second_cohomology_order :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        ∏ ω : MulAction.orbitRel.Quotient G ι, Nat.card (MulAction.stabilizer G ω.out) := by
  have hf (ω : MulAction.orbitRel.Quotient G ι) :=
    transitivePermutation_second_cohomology_order G ω.orbit (permutationOrbitPoint G ι ω)
  letI (ω : MulAction.orbitRel.Quotient G ι) :
      Finite (groupCohomology (permutationCoordinateRep ℤ G ω.orbit) 2) := (hf ω).1
  let e := (permutationOrbitCohomologyIso G ι ℤ 2).toLinearEquiv.toEquiv
  refine ⟨Finite.of_equiv (∀ ω : MulAction.orbitRel.Quotient G ι,
    groupCohomology (permutationCoordinateRep ℤ G ω.orbit) 2) e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_pi]
  apply Finset.prod_congr rfl
  intro ω _
  simpa only [permutationOrbitPoint_stabilizer] using (hf ω).2

end
end Dubon2026
