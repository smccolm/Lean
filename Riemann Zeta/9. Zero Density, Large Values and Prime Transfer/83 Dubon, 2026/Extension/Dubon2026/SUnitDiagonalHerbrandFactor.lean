import Dubon2026.SUnitDiagonalCohomologySequence
import Dubon2026.CyclicCohomologyHerbrandMultiplicativity
import Dubon2026.CyclicIntegerEvenCohomology

/-! # The actual integer diagonal factor in S-unit cohomology

The proved original diagonal splitting, its cohomology retraction, and
the original cyclic integer cohomology compute the factor of the group
order between extended and logarithmic lattices. Only finiteness for
the actual extended lattice remains upstream, to be supplied by its
proved finite-index permutation sublattice. This serves DUB-17's S-unit
Herbrand calculation and subsequent global norm-index lower bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original integer diagonal contributes exactly the Galois group order to the actual lattice Herbrand cardinality. -/
theorem sUnit_diagonal_herbrand_factor
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) * Nat.card Gal(L/K) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : IsCyclic Gal(L/K) := ⟨⟨σ, hgen⟩⟩
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI : Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1) :=
    sUnitLogLattice_cohomology_finite_of_extended K L S hS 1
  letI : Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2) :=
    sUnitLogLattice_cohomology_finite_of_extended K L S hS 2
  refine ⟨inferInstance, inferInstance, ?_⟩
  let X := sUnitDiagonalShortComplex K L S hS
  letI : Finite (groupCohomology X.X₁ 1) :=
    inferInstanceAs (Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1))
  letI : Finite (groupCohomology X.X₁ 2) :=
    inferInstanceAs (Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2))
  letI : Subsingleton (groupCohomology X.X₃ 1) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (cyclic_trivial_integer_odd_cohomology_zero Gal(L/K) σ hgen 1 (by decide))
  letI : Finite (groupCohomology X.X₃ 1) := Finite.of_subsingleton
  have hz2 := cyclic_trivial_integer_even_cohomology_order Gal(L/K) σ hgen 2 (by decide)
  letI : Finite (groupCohomology X.X₃ 2) := hz2.1
  have hz1 : Nat.card (groupCohomology X.X₃ 1) = 1 := Nat.card_unique
  have h := (cyclic_cohomology_herbrand_cardinality X
    (sUnitDiagonalShortComplex_shortExact K L S hS) σ hgen).2.2
  rw [hz1, mul_one] at h
  change Nat.card (groupCohomology (sUnitLogProductRep K L S hS) 2) *
      Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
    Nat.card (groupCohomology (sUnitLogProductRep K L S hS) 1) *
      Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) *
      Nat.card (groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2) at h
  rw [hz2.2, ← Nat.card_eq_fintype_card] at h
  rw [Nat.card_congr (sUnitExtendedProductCohomologyIso K L S hS 2).toLinearEquiv.toEquiv,
    Nat.card_congr (sUnitExtendedProductCohomologyIso K L S hS 1).toLinearEquiv.toEquiv] at h
  exact h

end
end Dubon2026
