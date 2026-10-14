import Dubon2026.RationalPrimeChangedCyclotomicCompositum
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Local structure and an unramifiedness criterion for the actual changed compositum

The finite Galois compositum receives the spectral local-field structure over
the already realized changed auxiliary field.  A narrow converse to the
uniformizer preservation theorem reduces its formal unramifiedness to proving
that one actual auxiliary uniformizer remains irreducible upstairs.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Once the changed auxiliary field has its proved local structure, its
actual finite Galois cyclotomic compositum has the spectral finite-extension
local structure and extending valuation. -/
theorem rationalPrimeChangedCyclotomicCompositum_exists_local_structure
    (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)] :
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    let M := rationalPrimeChangedCyclotomicCompositum p hp n u
    ∃ (_ : ValuativeRel M) (_ : TopologicalSpace M)
      (_ : IsNonarchimedeanLocalField M)
      (_ : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)),
      True := by
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let M := rationalPrimeChangedCyclotomicCompositum p hp n u
  letI : FiniteDimensional E M :=
    (rationalPrimeChangedCyclotomicCompositum p hp n u).finiteDimensional
  haveI : Algebra.IsAlgebraic E M := Algebra.IsAlgebraic.of_finite E M
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  let normE := localFieldOriginalNorm E
  letI : NontriviallyNormedField E := normE
  letI : NormedField E := normE.toNormedField
  haveI : CompleteSpace E := localFieldOriginalNorm_complete E
  haveI : IsUltrametricDist E := localFieldOriginalNorm_isUltrametric E
  haveI : (NormedField.valuation (K := E)).Compatible :=
    localFieldOriginalNorm_compatible E
  letI : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField E M
  letI : NormedAlgebra E M := spectralNorm.normedAlgebra E M
  haveI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra E
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : IsNonarchimedeanLocalField M :=
    spectralFiniteExtension_isNonarchimedeanLocalField E M
  haveI : (ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M) :=
    spectralValuation_hasExtension E M
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, trivial⟩

/-- For a finite extension of nonarchimedean local fields, an actual base
uniformizer that remains irreducible upstairs forces formal unramifiedness of
the integer-ring extension.  Residue separability is automatic for the finite
residue fields; equality of maximal ideals follows from the two displayed
uniformizers. -/
theorem localField_integer_formallyUnramified_of_irreducible_algebraMap
    (E M : Type) [Field E] [Field M] [Algebra E M]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [Module.Finite 𝒪[E] 𝒪[M]]
    (π : 𝒪[E]) (hπ : Irreducible π)
    (hmap : Irreducible (algebraMap 𝒪[E] 𝒪[M] π)) :
    Algebra.FormallyUnramified 𝒪[E] 𝒪[M] := by
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer
      (algebraMap 𝒪[E] 𝒪[M] π)).mp hmap]

end
end Dubon2026
