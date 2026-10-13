import Dubon2026.SUnitExtendedLogLattice
import Dubon2026.FiniteIndexPermutationLattice

/-! # Finite-index permutation comparison for the original S-unit lattice

The preceding approximation and averaging construction is applied to
the actual stable complete logarithmic lattice with its integral diagonal.
The resulting full sublattice has finite index and a basis permuted by
the actual action on original places. This discharges the representation
comparison input to DUB-17's S-unit Herbrand calculation; the cohomological
cardinality formula itself remains a further obligation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual extended original S-unit logarithmic lattice has the required finite-index permutation basis. -/
theorem sUnit_exists_finiteIndex_permutation_sublattice :
    letI := sUnitLogPlaceAction K L S hS
    letI := sUnitFullLogSpaceAction K L S hS
    ∃ T : Submodule ℤ (SUnitFullLogSpace L S),
      T ≤ sUnitExtendedLogLattice L S ∧ DiscreteTopology T ∧
      Submodule.span ℝ (T : Set (SUnitFullLogSpace L S)) = ⊤ ∧
      Finite (sUnitExtendedLogLattice L S ⧸ T.comap (sUnitExtendedLogLattice L S).subtype) ∧
      ∃ b : Module.Basis (SUnitLogPlace L S) ℤ T,
        ∀ (σ : Gal(L/K)) (p : SUnitLogPlace L S),
          σ • (b p : SUnitFullLogSpace L S) = (b (σ • p) : SUnitFullLogSpace L S) := by
  letI := sUnitLogPlaceAction K L S hS
  letI := sUnitFullLogSpaceAction K L S hS
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI := sUnitExtendedLogLattice_discrete L S
  letI := sUnitExtendedLogLattice_isZLattice L S
  let ρ := MulAction.toPermHom Gal(L/K) (SUnitLogPlace L S)
  have hstable : ∀ (σ : Gal(L/K)) (z : SUnitFullLogSpace L S),
      z ∈ sUnitExtendedLogLattice L S → permutationRepresentation ρ σ z ∈ sUnitExtendedLogLattice L S :=
    fun σ z hz => sUnitExtendedLogLattice_galois_mem L S K hS σ z hz
  let T := permutationSublattice ρ (sUnitExtendedLogLattice L S) hstable
  refine ⟨T, permutationSublattice_le ρ _ hstable, inferInstance,
    permutationSublattice_span_eq_top ρ _ hstable,
    permutationSublattice_finite_quotient ρ _ hstable,
    permutationSublatticeBasis ρ _ hstable, ?_⟩
  intro σ p
  exact permutationSublatticeBasis_permuted ρ _ hstable σ p

end
end Dubon2026
