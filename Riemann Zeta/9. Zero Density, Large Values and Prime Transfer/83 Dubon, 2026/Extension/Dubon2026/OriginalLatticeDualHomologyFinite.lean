import Dubon2026.RationalCircleFiniteCharacters
import Dubon2026.OriginalLatticeIntegralDuality

/-! # Finite cardinalities in the actual lattice duality

DUB-17's relation-obstruction surjectivity needs the cardinality of the
literal norm quotient. The original lattice duality and its proved right
nondegeneracy identify the finite size of dual homology from actual H2.
No unproved comparison of the duality pairing with the H2 map is used.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M : Rep.{0} ℤ G)
  [Module.Finite ℤ M] [Module.Projective ℤ M] [Finite (groupCohomology M 2)]

/-- Finite original H2 and the actual separating lattice pairing force
first homology of the integral dual to be finite. -/
theorem originalLatticeDualHomology_finite :
    Finite (groupHomology (originalLinearCharacterRep ℤ M) 1) := by
  let H := groupCohomology M 2
  let D := groupHomology (originalLinearCharacterRep ℤ M) 1
  letI : Finite (H →ₗ[ℤ] AddCircle (1 : ℚ)) :=
    Finite.of_injective (originalRationalCircleFiniteCharacterEquiv H)
      (originalRationalCircleFiniteCharacterEquiv H).injective
  let f : D →ₗ[ℤ] (H →ₗ[ℤ] AddCircle (1 : ℚ)) :=
    (originalLatticeIntegralDuality M).toLinearMap.flip
  apply Finite.of_injective f
  apply (injective_iff_map_eq_zero f).mpr
  intro y hy
  apply originalLatticeIntegralDuality_right_nondegenerate M y
  intro x
  exact LinearMap.congr_fun hy x

/-- Actual dual homology and actual H2 have the same finite cardinality,
by the original lattice equivalence and pinned finite character duality. -/
theorem originalLatticeDualHomology_card :
    Nat.card (groupHomology (originalLinearCharacterRep ℤ M) 1) =
      Nat.card (groupCohomology M 2) := by
  letI := originalLatticeDualHomology_finite M
  exact (Nat.card_congr ((originalLatticeIntegralDuality M).toEquiv.trans
    (originalRationalCircleFiniteCharacterEquiv _))).symm

end
end Dubon2026
