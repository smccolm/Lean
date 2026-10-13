import Dubon2026.SUnitLogProductLattice

/-! # A complete stable lattice in the original place-permutation space

The original logarithmic lattice and one integral invariant diagonal
pull back to the actual all-place coordinate space. The exact splitting
is equivariant, so the pullback is stable under its original permutation
action. This is the required lattice for DUB-17's finite-index
permutation comparison and S-unit Herbrand calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

/-- The original diagonal splitting as a continuous equivalence. -/
def sUnitLogDiagonalContinuousEquiv :
    SUnitFullLogSpace L S ≃L[ℝ] SUnitLogHyperplane L S × ℝ :=
  (sUnitLogDiagonalEquiv L S).toContinuousLinearEquiv

/-- The original full logarithmic lattice extended by its integral invariant diagonal. -/
def sUnitExtendedLogLattice : Submodule ℤ (SUnitFullLogSpace L S) :=
  ZLattice.comap ℝ (sUnitLogProductLattice L S) (sUnitLogDiagonalContinuousEquiv L S).toLinearMap

/-- Membership in the original extended lattice uses exactly the original split coordinates. -/
theorem sUnitExtendedLogLattice_mem (z : SUnitFullLogSpace L S) :
    z ∈ sUnitExtendedLogLattice L S ↔
      (sUnitLogDiagonalSplit L S z).1 ∈ sUnitFullLogLattice L S ∧
        ∃ n : ℤ, (n : ℝ) = sUnitLogCoordinateSum L S z :=
  sUnitLogProductLattice_mem L S (sUnitLogDiagonalSplit L S z)

/-- The original extended lattice is discrete in the original all-place coordinate space. -/
theorem sUnitExtendedLogLattice_discrete : DiscreteTopology (sUnitExtendedLogLattice L S) := by
  letI := sUnitLogProductLattice_discrete L S
  unfold sUnitExtendedLogLattice
  infer_instance

/-- The original extended lattice spans the entire original all-place permutation space. -/
theorem sUnitExtendedLogLattice_isZLattice :
    letI := sUnitExtendedLogLattice_discrete L S
    IsZLattice ℝ (sUnitExtendedLogLattice L S) := by
  letI := sUnitLogProductLattice_discrete L S
  letI := sUnitLogProductLattice_isZLattice L S
  unfold sUnitExtendedLogLattice
  infer_instance

variable (K : Type) [Field K] [Algebra K L]
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original hyperplane component of the diagonal splitting is Galois-equivariant. -/
theorem sUnitLogDiagonalSplit_fst_galois (σ : Gal(L/K)) (z : SUnitFullLogSpace L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    letI := sUnitLogHyperplaneAction K L S hS
    (sUnitLogDiagonalSplit L S (σ • z)).1 = σ • (sUnitLogDiagonalSplit L S z).1 := by
  letI := sUnitLogPlaceAction K L S hS
  letI := sUnitFullLogSpaceAction K L S hS
  apply Subtype.ext
  funext p
  change z (σ⁻¹ • p) - sUnitLogCoordinateSum L S (σ • z) *
      (Fintype.card (SUnitLogPlace L S) : ℝ)⁻¹ =
    z (σ⁻¹ • p) - sUnitLogCoordinateSum L S z * (Fintype.card (SUnitLogPlace L S) : ℝ)⁻¹
  rw [sUnitLogCoordinateSum_galois]

/-- The actual complete extended logarithmic lattice is stable under the original place permutation. -/
theorem sUnitExtendedLogLattice_galois_mem (σ : Gal(L/K)) (z : SUnitFullLogSpace L S)
    (hz : z ∈ sUnitExtendedLogLattice L S) :
    letI := sUnitFullLogSpaceAction K L S hS
    σ • z ∈ sUnitExtendedLogLattice L S := by
  rw [sUnitExtendedLogLattice_mem] at hz ⊢
  rw [sUnitLogDiagonalSplit_fst_galois, sUnitLogCoordinateSum_galois]
  exact ⟨sUnitFullLogLattice_galois_mem K L S hS σ _ hz.1, hz.2⟩

end
end Dubon2026
