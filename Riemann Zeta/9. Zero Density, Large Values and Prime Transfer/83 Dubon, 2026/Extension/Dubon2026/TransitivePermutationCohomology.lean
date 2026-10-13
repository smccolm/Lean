import Dubon2026.TransitivePermutationCoinduction
import Dubon2026.CyclicIntegerEvenCohomology

/-! # Original cohomology of one finite cyclic permutation orbit

The actual stabilizer is cyclic. Existing Shapiro and original cyclic
integer cohomology prove H1 is zero and H2 has exactly the stabilizer
order. These are the orbit factors needed for the actual S-unit
finite-index permutation lattice in DUB-17's norm-index argument.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (G ι : Type) [CommGroup G] [Fintype G] [IsCyclic G]
  [MulAction G ι] [MulAction.IsPretransitive G ι] (i : ι)
include i

/-- Original H1 of a transitive integral permutation representation is zero. -/
theorem transitivePermutation_first_cohomology_zero :
    Limits.IsZero (groupCohomology (permutationCoordinateRep ℤ G ι) 1) := by
  let H := MulAction.stabilizer G i
  letI : Fintype H := Fintype.ofFinite _
  obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := H)
  exact (cyclic_trivial_integer_odd_cohomology_zero H h hh 1 (by decide)).of_iso
    (transitivePermutationCohomologyIso ℤ G ι i 1)

/-- Original H2 of a transitive integral permutation representation is finite and has exactly the actual stabilizer order. -/
theorem transitivePermutation_second_cohomology_order :
    Finite (groupCohomology (permutationCoordinateRep ℤ G ι) 2) ∧
      Nat.card (groupCohomology (permutationCoordinateRep ℤ G ι) 2) =
        Nat.card (MulAction.stabilizer G i) := by
  let H := MulAction.stabilizer G i
  letI : Fintype H := Fintype.ofFinite _
  obtain ⟨h, hh⟩ := IsCyclic.exists_generator (α := H)
  have he := cyclic_trivial_integer_even_cohomology_order H h hh 2 (by decide)
  letI := he.1
  let e := (transitivePermutationCohomologyIso ℤ G ι i 2).toLinearEquiv.toEquiv
  refine ⟨Finite.of_equiv (groupCohomology (Rep.trivial ℤ H ℤ) 2) e.symm, ?_⟩
  exact (Nat.card_congr e).trans (he.2.trans (Nat.card_eq_fintype_card (α := H)).symm)

end
end Dubon2026
